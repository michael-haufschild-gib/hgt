import GaloisForLFunctions.HTGeometry.ScalarClockCharacterDichotomy
import GaloisForLFunctions.HTGeometry.StableCoreFunctoriality

/-!
# The clock-character dichotomy at the persistent core `T = ∩ₙ Φⁿ(F)`

Instantiating the abstract dichotomy at the actual persistent core: the stable range core
`T = stableRangeCore Φ` of an injective differential endomorphism `Φ` of a scalar free differential
field `F`.  The corpus stable-core machinery supplies exactly the structure the dichotomy needs:

* `T` is a differential subfield (`derivationClosed_stableRangeCore`), so it carries a `Differential`
  instance and is a differential `C`-algebra;
* `Φ` restricts to a differential *automorphism* `Φ|T` (`stableRangeCoreDifferentialAlgEquiv`).

Hence, on the persistent core `T = C⟨q⟩`, a positive-charge clock forces `Φ|T(q) = a·q`.  The only
remaining hypotheses are the differential Lüroth generator `q` (with its charge) and the
diagonalized clock action on it.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- **The clock-character dichotomy at the persistent core.**  For an injective differential
endomorphism `Φ` of a scalar free differential field `F`, on its stable range core `T = ∩ₙ Φⁿ(F)`,
generated as a differential field by a single differential-transcendental `q` (`T = C⟨q⟩`, the
differential Lüroth output), a clock cocharacter of charge `k` forces the restricted automorphism
`Φ|T` to act on `q` by a Möbius transform (eq. 3), and to be multiplication by one constant when the
charge is positive (eq. 4). -/
theorem persistent_core_clock_character_dichotomy
    {C F : Type*} [Field C] [IsAlgClosed C] [Field F] [CharZero F]
    [Differential C] [Differential F] [Algebra C F] [DifferentialAlgebra C F]
    (φ : F →ₐ[C] F) (hφ : ∀ x : F, φ x′ = (φ x)′) :
    letI : Differential (stableRangeCore φ) :=
      derivationClosedDifferential _ (derivationClosed_stableRangeCore φ hφ)
    ∀ (ρT : C → (stableRangeCore φ →ₐ[C] stableRangeCore φ)) {q : stableRangeCore φ} {k : ℕ},
      HypertranscendentalOver C q →
      differentialAdjoin C ({q} : Set (stableRangeCore φ)) = ⊤ →
      (∀ lam : C, lam ≠ 0 →
        ρT lam q = algebraMap C (stableRangeCore φ) (lam ^ k) * q) →
      (∀ lam mu : C, lam ≠ 0 → mu ≠ 0 → ρT (lam * mu) q = ρT lam (ρT mu q)) →
      (∀ lam : C, lam ≠ 0 →
        (stableRangeCoreDifferentialAlgEquiv φ hφ).toAlgEquiv.toAlgHom (ρT lam q)
          = ρT lam ((stableRangeCoreDifferentialAlgEquiv φ hφ).toAlgEquiv.toAlgHom q)) →
      (∃ a b c d : C, a * d - b * c ≠ 0 ∧
          (stableRangeCoreDifferentialAlgEquiv φ hφ).toAlgEquiv q
              * (algebraMap C (stableRangeCore φ) c * q + algebraMap C (stableRangeCore φ) d)
            = algebraMap C (stableRangeCore φ) a * q + algebraMap C (stableRangeCore φ) b)
        ∧ (0 < k → ∃ a : C,
            (stableRangeCoreDifferentialAlgEquiv φ hφ).toAlgEquiv q
              = algebraMap C (stableRangeCore φ) a * q) := by
  letI : Differential (stableRangeCore φ) :=
    derivationClosedDifferential _ (derivationClosed_stableRangeCore φ hφ)
  haveI : DifferentialAlgebra C (stableRangeCore φ) := by
    refine ⟨fun c => ?_⟩
    apply Subtype.ext
    rw [derivationClosedDifferential_apply]
    show ((algebraMap C F c))′ = ((algebraMap C F c′))
    exact DifferentialAlgebra.deriv_algebraMap c
  intro ρT q k hq hqtop hcharge hmulρ hcomm
  exact persistent_clock_character_dichotomy
    (stableRangeCoreDifferentialAlgEquiv φ hφ).toAlgEquiv ρT hq hqtop
    (stableRangeCoreDifferentialAlgEquiv φ hφ).map_deriv' hcharge hmulρ hcomm

end GaloisForLFunctions.HTGeometry
