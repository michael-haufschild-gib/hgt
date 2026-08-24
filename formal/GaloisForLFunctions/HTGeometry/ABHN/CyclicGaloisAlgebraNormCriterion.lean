/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraSplit
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative
open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

theorem cyclicNormFactor_generator_map_mul (sigma : L ≃+* L) (c : L) (m : ℕ) :
    sigma (cyclicNormFactor sigma c m) * c = cyclicNormFactor sigma c (m + 1) := by
  induction m with
  | zero => simp [cyclicNormFactor_zero, cyclicNormFactor_succ]
  | succ m ih =>
      rw [cyclicNormFactor_succ, map_mul]
      have hpow : sigma ((sigma ^ m) c) = (sigma ^ (m + 1)) c := by
        rw [pow_succ']
        rfl
      rw [hpow, cyclicNormFactor_succ]
      calc
        sigma (cyclicNormFactor sigma c m) * (sigma ^ (m + 1)) c * c =
            (sigma (cyclicNormFactor sigma c m) * c) * (sigma ^ (m + 1)) c := by
              ac_rfl
        _ = cyclicNormFactor sigma c (m + 1) * (sigma ^ (m + 1)) c := by rw [ih]

/-- Orbit map obtained from a splitting representation and the coefficient-field orbit of `1`. -/
noncomputable def cyclicGaloisAlgebraSplittingOrbitLinearMap (a : K)
    (e : cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) : L →ₗ[K] L where
  toFun b := e (cyclicGaloisAlgebraC K L a b) 1
  map_add' b d := by
    change e ((cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a)) (b + d)) 1 = _
    rw [map_add, map_add]
    rfl
  map_smul' r b := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    calc
      e (cyclicGaloisAlgebraC K L a (algebraMap K L r * b)) 1 =
          e (algebraMap K (cyclicGaloisAlgebra K L a) r *
            cyclicGaloisAlgebraC K L a b) 1 := by
              rw [cyclicGaloisAlgebra_algebraMap_apply, cyclicAlgebraC_mul]
      _ = (algebraMap K L r) * e (cyclicGaloisAlgebraC K L a b) 1 := by
        rw [map_mul, e.commutes]
        simp [Module.End.mul_apply, Algebra.smul_def]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem cyclicGaloisAlgebraSplittingOrbitLinearMap_apply (a : K)
    (e : cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) (b : L) :
    cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e b =
      e (cyclicGaloisAlgebraC K L a b) 1 := rfl

omit [FiniteDimensional K L] [IsGalois K L] in
theorem cyclicGaloisAlgebraSplittingOrbitLinearMap_injective (a : K)
    (e : cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) :
    Function.Injective (cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e) := by
  intro b d hbd
  apply sub_eq_zero.mp
  by_contra hne
  have hz : cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e (b - d) = 0 := by
    rw [map_sub, hbd, sub_self]
  have hunitC : IsUnit (cyclicGaloisAlgebraC K L a (b - d)) := by
    change IsUnit ((cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a)) (b - d))
    exact IsUnit.map _ (Ne.isUnit hne)
  have hunitE : IsUnit (e (cyclicGaloisAlgebraC K L a (b - d))) :=
    IsUnit.map e.toRingHom hunitC
  have hinj : Function.Injective (e (cyclicGaloisAlgebraC K L a (b - d))) :=
    ((Module.End.isUnit_iff _).mp hunitE).1
  have hone : e (cyclicGaloisAlgebraC K L a (b - d)) 1 = 0 := hz
  have : (1 : L) = 0 := hinj (by simpa using hone)
  exact one_ne_zero this

/-- The coefficient-field orbit of `1` is a linear coordinate system on a split cyclic
algebra representation. -/
noncomputable def cyclicGaloisAlgebraSplittingOrbitLinearEquiv (a : K)
    (e : cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) : L ≃ₗ[K] L :=
  LinearEquiv.ofInjectiveEndo (cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e)
    (cyclicGaloisAlgebraSplittingOrbitLinearMap_injective K L a e)

omit [IsGalois K L] in
theorem cyclicGaloisAlgebraSplittingOrbitLinearEquiv_apply (a : K)
    (e : cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) (b : L) :
    cyclicGaloisAlgebraSplittingOrbitLinearEquiv K L a e b =
      cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e b := rfl

/-- Coefficient by which the cyclic generator twists the regular coefficient-field action in
orbit coordinates. -/
noncomputable def cyclicGaloisAlgebraSplittingParameter (a : K)
    (e : cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) : L :=
  (cyclicGaloisAlgebraSplittingOrbitLinearEquiv K L a e).symm
    (e (cyclicGaloisAlgebraX K L a) 1)

omit [IsGalois K L] in
theorem cyclicGaloisAlgebraSplittingParameter_spec (a : K)
    (e : cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) :
    cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e
        (cyclicGaloisAlgebraSplittingParameter K L a e) =
      e (cyclicGaloisAlgebraX K L a) 1 := by
  change cyclicGaloisAlgebraSplittingOrbitLinearEquiv K L a e
      ((cyclicGaloisAlgebraSplittingOrbitLinearEquiv K L a e).symm
        (e (cyclicGaloisAlgebraX K L a) 1)) = _
  exact (cyclicGaloisAlgebraSplittingOrbitLinearEquiv K L a e).apply_symm_apply _

omit [IsGalois K L] in
/-- In orbit coordinates, the cyclic generator acts as `b ↦ σ(b)c`. -/
theorem cyclicGaloisAlgebraSplittingGenerator_apply_orbit (a : K)
    (e : cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) (b : L) :
    e (cyclicGaloisAlgebraX K L a)
        (cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e b) =
      cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e
        (cyclicGaloisGenerator K L b * cyclicGaloisAlgebraSplittingParameter K L a e) := by
  let c := cyclicGaloisAlgebraSplittingParameter K L a e
  calc
    e (cyclicGaloisAlgebraX K L a)
        (cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e b) =
        e (cyclicGaloisAlgebraX K L a * cyclicGaloisAlgebraC K L a b) 1 := by
      rw [cyclicGaloisAlgebraSplittingOrbitLinearMap_apply, map_mul]
      rfl
    _ = e (cyclicGaloisAlgebraC K L a (cyclicGaloisGenerator K L b) *
          cyclicGaloisAlgebraX K L a) 1 := by
      exact congrArg (fun z : cyclicGaloisAlgebra K L a ↦ e z 1)
        (cyclicAlgebraX_mul_cyclicAlgebraC
          L (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
          (algebraMap K L a) b)
    _ = e (cyclicGaloisAlgebraC K L a (cyclicGaloisGenerator K L b))
          (e (cyclicGaloisAlgebraX K L a) 1) := by
      rw [map_mul]
      rfl
    _ = e (cyclicGaloisAlgebraC K L a (cyclicGaloisGenerator K L b))
          (cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e c) := by
      rw [cyclicGaloisAlgebraSplittingParameter_spec]
    _ = e (cyclicGaloisAlgebraC K L a
          (cyclicGaloisGenerator K L b * c)) 1 := by
      rw [cyclicGaloisAlgebraSplittingOrbitLinearMap_apply,
        ← Module.End.mul_apply, ← map_mul, cyclicAlgebraC_mul]
    _ = cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e
          (cyclicGaloisGenerator K L b * c) := rfl

omit [IsGalois K L] in
/-- Iterating the split cyclic generator on `1` records the product of conjugates of its orbit
parameter. -/
theorem cyclicGaloisAlgebraSplittingGenerator_pow_apply_one (a : K)
    (e : cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) (m : ℕ) :
    (e (cyclicGaloisAlgebraX K L a) ^ m) 1 =
      cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e
        (cyclicNormFactor (cyclicGaloisGenerator K L).toRingEquiv
          (cyclicGaloisAlgebraSplittingParameter K L a e) m) := by
  induction m with
  | zero =>
      rw [pow_zero, Module.End.one_apply, cyclicNormFactor_zero,
        cyclicGaloisAlgebraSplittingOrbitLinearMap_apply]
      change 1 = e (cyclicAlgebraC (cyclicGaloisGenerator K L).toRingEquiv
        (Module.finrank K L) (algebraMap K L a) 1) 1
      rw [cyclicAlgebraC_one]
      exact congrArg (fun f : Module.End K L ↦ f 1) (map_one e).symm
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih,
        cyclicGaloisAlgebraSplittingGenerator_apply_orbit]
      apply congrArg (cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e)
      change (cyclicGaloisGenerator K L).toRingEquiv
          (cyclicNormFactor (cyclicGaloisGenerator K L).toRingEquiv
            (cyclicGaloisAlgebraSplittingParameter K L a e) m) *
          cyclicGaloisAlgebraSplittingParameter K L a e = _
      exact cyclicNormFactor_generator_map_mul L (cyclicGaloisGenerator K L).toRingEquiv
        (cyclicGaloisAlgebraSplittingParameter K L a e) m

/-- The parameter extracted from any splitting representation has norm equal to the defining
cyclic-algebra parameter. -/
theorem cyclicGaloisAlgebraSplittingParameter_norm (a : K)
    (e : cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) :
    a = Algebra.norm K (cyclicGaloisAlgebraSplittingParameter K L a e) := by
  have horbit :
      cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e (algebraMap K L a) =
        cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e
          (cyclicNormFactor (cyclicGaloisGenerator K L).toRingEquiv
            (cyclicGaloisAlgebraSplittingParameter K L a e) (Module.finrank K L)) := by
    calc
      cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e (algebraMap K L a) =
          e (cyclicGaloisAlgebraC K L a (algebraMap K L a)) 1 := rfl
      _ = e (cyclicGaloisAlgebraX K L a ^ Module.finrank K L) 1 := by
        exact congrArg (fun z : cyclicGaloisAlgebra K L a ↦ e z 1)
          (cyclicGaloisAlgebraX_pow K L a).symm
      _ = (e (cyclicGaloisAlgebraX K L a) ^ Module.finrank K L) 1 := by
        rw [map_pow]
      _ = cyclicGaloisAlgebraSplittingOrbitLinearMap K L a e
          (cyclicNormFactor (cyclicGaloisGenerator K L).toRingEquiv
            (cyclicGaloisAlgebraSplittingParameter K L a e) (Module.finrank K L)) :=
        cyclicGaloisAlgebraSplittingGenerator_pow_apply_one K L a e (Module.finrank K L)
  have hcoeff : algebraMap K L a =
      cyclicNormFactor (cyclicGaloisGenerator K L).toRingEquiv
        (cyclicGaloisAlgebraSplittingParameter K L a e) (Module.finrank K L) :=
    cyclicGaloisAlgebraSplittingOrbitLinearMap_injective K L a e horbit
  apply FaithfulSMul.algebraMap_injective K L
  calc
    algebraMap K L a = cyclicNormFactor (cyclicGaloisGenerator K L).toRingEquiv
        (cyclicGaloisAlgebraSplittingParameter K L a e) (Module.finrank K L) := hcoeff
    _ = algebraMap K L
        (Algebra.norm K (cyclicGaloisAlgebraSplittingParameter K L a e)) :=
      cyclicGaloisNormFactor_eq_algebraMap_norm K L
        (cyclicGaloisAlgebraSplittingParameter K L a e)

/-- For a nonzero cyclic parameter, the coefficient extracted from a splitting is a unit. -/
theorem cyclicGaloisAlgebraSplittingParameter_ne_zero (a : K) (ha : a ≠ 0)
    (e : cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) :
    cyclicGaloisAlgebraSplittingParameter K L a e ≠ 0 := by
  intro hc
  apply ha
  calc
    a = Algebra.norm K (cyclicGaloisAlgebraSplittingParameter K L a e) :=
      cyclicGaloisAlgebraSplittingParameter_norm K L a e
    _ = 0 := by rw [hc, Algebra.norm_zero]

/-- Unit-valued norm witness extracted from a splitting. -/
noncomputable def cyclicGaloisAlgebraSplittingNormUnit (a : K) (ha : a ≠ 0)
    (e : cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) : Lˣ :=
  Units.mk0 (cyclicGaloisAlgebraSplittingParameter K L a e)
    (cyclicGaloisAlgebraSplittingParameter_ne_zero K L a ha e)

theorem cyclicGaloisAlgebraSplittingNormUnit_norm (a : K) (ha : a ≠ 0)
    (e : cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) :
    a = Algebra.norm K (cyclicGaloisAlgebraSplittingNormUnit K L a ha e : L) :=
  cyclicGaloisAlgebraSplittingParameter_norm K L a e

/-- **Norm criterion for cyclic algebras.** A nonzero cyclic Galois algebra is a full matrix
algebra over `K` exactly when its defining parameter is a norm from `L`. -/
theorem cyclicGaloisAlgebra_split_iff_exists_normUnit (a : K) (ha : a ≠ 0) :
    Nonempty (cyclicGaloisAlgebra K L a ≃ₐ[K] Module.End K L) ↔
      ∃ c : Lˣ, a = Algebra.norm K (c : L) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨cyclicGaloisAlgebraSplittingNormUnit K L a ha e,
      cyclicGaloisAlgebraSplittingNormUnit_norm K L a ha e⟩
  · rintro ⟨c, hc⟩
    refine ⟨(cyclicGaloisAlgebraNormScaleAlgEquiv K L a 1 c ?_).trans
      (cyclicGaloisAlgebraSplitAlgEquiv K L)⟩
    simpa using hc

/-- A selected cyclic `H²` algebra is explicitly split exactly for the zero cohomology class.
This is the representative-level injectivity of the cyclic crossed-product construction. -/
theorem cyclicGaloisH2ClassCyclicAlgebra_split_iff_eq_zero (z : cyclicGaloisH2 K L) :
    Nonempty (cyclicGaloisH2ClassCyclicAlgebra K L z ≃ₐ[K] Module.End K L) ↔ z = 0 := by
  let u : Kˣ := cyclicGaloisH2FixedBaseUnit K L (cyclicGaloisH2Representative K L z)
  change Nonempty (cyclicGaloisAlgebra K L (u : K) ≃ₐ[K] Module.End K L) ↔ z = 0
  rw [cyclicGaloisAlgebra_split_iff_exists_normUnit K L (u : K) u.ne_zero]
  constructor
  · rintro ⟨c, hc⟩
    have hproj : cyclicGaloisH2BaseProjection K L (Additive.ofMul u) =
        cyclicGaloisH2BaseProjection K L 0 :=
      (cyclicGaloisH2BaseProjection_eq_iff_exists_norm_ratio K L
        (Additive.ofMul u) 0).mpr ⟨c, by simpa using hc⟩
    have hu : u = cyclicGaloisH2FixedBaseUnit K L
        (cyclicGaloisH2Representative K L z) := rfl
    rw [hu, cyclicGaloisH2ClassCyclicAlgebra_baseParameter_projection, map_zero] at hproj
    exact hproj
  · intro hz
    have hproj : cyclicGaloisH2BaseProjection K L (Additive.ofMul u) =
        cyclicGaloisH2BaseProjection K L 0 := by
      have hu : u = cyclicGaloisH2FixedBaseUnit K L
          (cyclicGaloisH2Representative K L z) := rfl
      rw [hu, cyclicGaloisH2ClassCyclicAlgebra_baseParameter_projection, hz, map_zero]
    obtain ⟨c, hc⟩ := (cyclicGaloisH2BaseProjection_eq_iff_exists_norm_ratio K L
      (Additive.ofMul u) 0).mp hproj
    exact ⟨c, by simpa using hc⟩

/-- In any finite cyclic norm-quotient coordinates, the selected cyclic algebra is explicitly
split exactly at the zero coordinate. -/
theorem cyclicGaloisNormQuotientClassCyclicAlgebra_split_iff_eq_zero (n : ℕ)
    (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n) (z : ZMod n) :
    Nonempty
      (cyclicGaloisH2ClassCyclicAlgebra K L
          (cyclicGaloisH2BaseNormQuotientEquiv K L (e.symm z)) ≃ₐ[K] Module.End K L) ↔
      z = 0 := by
  rw [cyclicGaloisH2ClassCyclicAlgebra_split_iff_eq_zero]
  constructor
  · intro hz
    have hz' : cyclicGaloisH2BaseNormQuotientEquiv K L (e.symm z) =
        cyclicGaloisH2BaseNormQuotientEquiv K L 0 := by simpa using hz
    have hquot : e.symm z = 0 :=
      (cyclicGaloisH2BaseNormQuotientEquiv K L).injective hz'
    apply e.symm.injective
    simpa using hquot
  · rintro rfl
    simp


end GaloisForLFunctions.HTGeometry.ABHN
