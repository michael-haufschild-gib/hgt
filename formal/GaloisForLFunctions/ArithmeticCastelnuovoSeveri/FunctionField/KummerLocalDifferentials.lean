import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationDifferentials
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerUniformizerDifferentials

/-!
# Local regularity in a uniformizer coordinate

In a prime-power Kummer field the image of the local Kähler module is
exactly the integral multiples of the parameter differential. Frobenius
expansions prove the inclusion for generators; the reverse inclusion is
the image of the corresponding local differential.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.HTGeometry

/-- The actual local Kähler image consists exactly of integral multiples of `dπ`. -/
theorem squareKummer_mem_localDifferentials_iff
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (v : Valuation (SquareKummerField p s c b R) (WithZero (Multiplicative ℤ)))
    (hK : ∀ a : SquareConstantField p s,
      algebraMap (SquareConstantField p s) (SquareKummerField p s c b R) a ∈ v.valuationSubring)
    (π : SquareKummerField p s c b R) (hπ : v π = WithZero.exp (-1 : ℤ))
    (ω : KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R)) :
    ω ∈ valuationLocalDifferentials v.valuationSubring hK ↔
      ∃ a : SquareKummerField p s c b R, v a ≤ 1 ∧
        ω = a • KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R) π := by
  let K := SquareConstantField p s
  let L := SquareKummerField p s c b R
  let W := v.valuationSubring
  letI := valuationConstantAlgebra W hK
  let f := valuationConstantInclusion W hK
  change (∃ η : KaehlerDifferential K W, algHomKaehlerMap f η = ω) ↔ _
  constructor
  · rintro ⟨η, rfl⟩
    have hη : η ∈ Submodule.span W (Set.range (KaehlerDifferential.D K W)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hη
    · rintro _ ⟨x, rfl⟩
      rw [algHomKaehlerMap_D]
      exact squareKummer_integral_differential_uniformizer_multiple p s c b R v π hπ x x.property
    · exact ⟨0, by rw [map_zero]; exact zero_le_one, by rw [map_zero, zero_smul]⟩
    · intro η ξ _ _ hη hξ
      obtain ⟨a, ha, hη⟩ := hη
      obtain ⟨b, hb, hξ⟩ := hξ
      refine ⟨a + b, ?_, ?_⟩
      · exact (v.map_add a b).trans (max_le ha hb)
      · rw [map_add, hη, hξ, add_smul]
    · intro a η _ hη
      obtain ⟨b, hb, hη⟩ := hη
      refine ⟨(a : L) * b, ?_, ?_⟩
      · exact show (a : L) * b ∈ W from mul_mem a.property hb
      · rw [algHomKaehlerMap_smul, hη, mul_smul]
        rfl
  · rintro ⟨a, ha, rfl⟩
    have hπmem : π ∈ W := by
      change v π ≤ 1
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    refine ⟨(⟨a, ha⟩ : W) • KaehlerDifferential.D K W ⟨π, hπmem⟩, ?_⟩
    rw [algHomKaehlerMap_smul, algHomKaehlerMap_D]
    rfl

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
