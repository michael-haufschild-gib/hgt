import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedTypesCompatibility
import GaloisForLFunctions.HTGeometry.FinitePlaceTransport

/-! The normalized type equivalence transports complete splitting from the
ray field in the algebraic closure to the ray field of the host. -/

noncomputable section
open NumberField IsDedekindDomain GaloisForLFunctions
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace WindowedLandauTheory.NormalizedTypes

def RayCFT (K : RatField) (m : ℕ) : Prop := RayAdm K m (rayField K m)

variable {D : D7} {jE : D.host.E →+* AlgebraicClosure ℚ}

/-- The ray field equivalence preserves the number of places over a rational prime. -/
theorem splitsIn_mrayC_iff (T : NormalizedTypesCompatibility D jE) (p : ℕ) :
    SplitsIn (MrayC D jE) p ↔ (placesOver D.ntypes.Mray p).ncard = Module.finrank ℚ D.ntypes.Mray := by
  let f := RingOfIntegers.mapRingEquiv T.eM
  let e := heightOneSpectrumEquiv f
  have he (v : HeightOneSpectrum (𝓞 D.ntypes.Mray)) :
      (p : 𝓞 (MrayC D jE)) ∈ (e v).asIdeal ↔ (p : 𝓞 D.ntypes.Mray) ∈ v.asIdeal := by
    change f.symm (p : 𝓞 (MrayC D jE)) ∈ v.asIdeal ↔ _
    rw [map_natCast]
  have hcard : (placesOver D.ntypes.Mray p).ncard =
      ({v : HeightOneSpectrum (𝓞 (MrayC D jE)) | (p : 𝓞 (MrayC D jE)) ∈ v.asIdeal}).ncard := by
    refine Set.ncard_congr (fun v _ => e v) (fun v hv => (he v).2 hv)
      (fun _ _ _ _ h => e.injective h) ?_
    intro v hv
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    apply (he _).1
    rwa [e.apply_symm_apply]
  have hfin := T.eM.toRatAlgEquiv.toLinearEquiv.finrank_eq
  rw [SplitsIn, ← hcard, ← hfin]

/-- A principal generator congruent to one modulo a positive power of the modulus
also satisfies the splitting criterion for the modulus itself. -/
theorem mrayRay_of_tied (T : NormalizedTypesCompatibility D jE) (hC : RayCFT (KQbar D jE) D.ntypes.cond)
    (a : ℕ) (ha : 1 ≤ a) : MrayRay D a := by
  rintro p hp ⟨π, hπK, hπp, hπ1⟩
  apply (splitsIn_mrayC_iff T p).1
  apply hC.2.2
  refine ⟨hp, jE π, ⟨π, hπK, rfl⟩, (RingOfIntegers.isIntegral_coe π).map jE.toIntAlgHom, ?_, ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hπ1
    let N : AlgebraicClosure ℚ := D.ntypes.cond
    have he : jE (c : D.host.E) * N ^ (b + 1) = jE (π : D.host.E) - 1 := by
      have h := congrArg (fun x : 𝓞 D.host.E => jE (algebraMap (𝓞 D.host.E) D.host.E x)) hc
      simpa only [map_mul, map_sub, map_one, map_natCast, Nat.cast_pow] using h
    have hN : N ≠ 0 := by
      apply Nat.cast_ne_zero.mpr
      exact (Nat.mul_pos (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos) D.host.hyp.2.1.pos).ne'
    have hdiv : (jE (π : D.host.E) - 1) / N = jE (c : D.host.E) * N ^ b := by
      rw [div_eq_iff hN, ← he, pow_succ, mul_assoc]
    have hNi : IsIntegral ℤ N := by
      change IsIntegral ℤ (D.ntypes.cond : AlgebraicClosure ℚ)
      rw [← map_natCast (algebraMap ℤ (AlgebraicClosure ℚ))]
      exact isIntegral_algebraMap
    change IsIntegral ℤ ((jE (π : D.host.E) - 1) / N)
    rw [hdiv]
    exact ((RingOfIntegers.isIntegral_coe c).map jE.toIntAlgHom).mul (hNi.pow b)
  · letI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _
    letI : Algebra D.host.E (AlgebraicClosure ℚ) := jE.toAlgebra
    letI : IsScalarTower ℚ D.host.E (AlgebraicClosure ℚ) :=
      IsScalarTower.of_algebraMap_eq fun x => congrFun (congrArg DFunLike.coe
        (Subsingleton.elim (algebraMap ℚ (AlgebraicClosure ℚ))
          ((algebraMap D.host.E (AlgebraicClosure ℚ)).comp (algebraMap ℚ D.host.E)))) x
    let c : D.host.E →ₐ[ℚ] D.host.E := D.host.conj
    refine ⟨c.liftNormal (AlgebraicClosure ℚ), ?_⟩
    have h := AlgHom.liftNormal_commutes c (AlgebraicClosure ℚ) (π : D.host.E)
    change c.liftNormal (AlgebraicClosure ℚ) (jE π) = jE (c π) at h
    rw [h, ← map_mul]
    change jE ((π : D.host.E) * D.host.conj (π : D.host.E)) = _
    rw [hπp, map_natCast]

end WindowedLandauTheory.NormalizedTypes
