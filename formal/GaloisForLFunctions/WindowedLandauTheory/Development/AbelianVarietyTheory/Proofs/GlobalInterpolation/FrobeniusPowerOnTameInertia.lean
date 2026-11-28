import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WildInertiaCriterion

/-! Arithmetic Frobenius acts on tame inertia by the residue-cardinality
power, including when the residue field is larger than its prime field. -/

noncomputable section

open NumberField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameKummer

/-- The difference between Frobenius conjugation and the residue-cardinality power
acts trivially on every prime-to-(p) radical, hence belongs to wild inertia. -/
theorem frobenius_conj_div_wild_of_card {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) {p : ℕ} [Fact p.Prime] (hp : A.valuation (p : Ω) < 1)
    {q : ℕ} {τ φ : G E Ω} (hτ : τ ∈ Ine (F := E) A) (hφ : IsFrob A q φ) :
    let δ := (τ ^ q)⁻¹ * (φ * τ * φ⁻¹)
    δ ∈ Ine (F := E) A ∧ ∀ y : Ω, y ≠ 0 → A.valuation (δ y / y - 1) < 1 := by
  letI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  letI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  letI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  let b := τ ^ q
  let δ := b⁻¹ * (φ * τ * φ⁻¹)
  have hb : b ∈ Ine (F := E) A := pow_mem hτ q
  have hδ : δ ∈ Ine (F := E) A := mul_mem (inv_mem hb) (conj_mem_Ine hφ.1 hτ)
  refine ⟨hδ, valuation_sub_one_lt_of_trivial_tame A hp hδ ?_⟩
  intro d hd
  let n := p ^ d - 1
  have hn : 0 < n := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  have hpn : p.Coprime n := coprime_pow_sub_one hd
  have hp₀ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (p : Ω) hn
  have hy₀ : y ≠ 0 := fun h => hp₀ (by simpa only [h, zero_pow hn.ne'] using hy.symm)
  let z := (φ⁻¹ : G E Ω) y
  have hz : z ^ n = (p : Ω) := by
    change ((φ⁻¹ : G E Ω) y) ^ n = _
    rw [← map_pow, hy, map_natCast]
  let μ := τ y / y
  have hm : μ ^ n = 1 := ratio_pow_eq_one τ hp₀ hy
  have hphiμ : φ μ = μ ^ q := by
    apply eq_of_pow_eq_one A (natCast_valuation_not_lt_one A hp hpn)
    · rw [← map_pow, hm, map_one]
    · rw [pow_right_comm, hm, one_pow]
    · exact hφ.2 μ (valuation_eq_one_of_pow_eq_one A hn.ne' hm).le
  have hc : (φ * τ * φ⁻¹) y / y = μ ^ q := by
    change φ (τ z) / y = _
    calc
      _ = φ (τ z / z) := by rw [map_div₀, show φ z = y from mul_inv_apply y]
      _ = μ ^ q := by
        rw [ratio_indep A hp hτ hn hpn hy hz]
        exact hphiμ
  have he : b * δ = φ * τ * φ⁻¹ := by dsimp [δ]; group
  have hr := ratio_mul A hp hb hn hpn δ hy
  rw [he, hc, show b y / y = μ ^ q from ratio_npow A hp hτ hn hpn hy q] at hr
  have hunit : δ y / y = 1 :=
    mul_left_cancel₀ (pow_ne_zero q (div_ne_zero ((map_ne_zero τ).mpr hy₀) hy₀))
      (hr.symm.trans (mul_one _).symm)
  exact ⟨y, hy, by rw [hunit, sub_self, map_zero]; exact zero_lt_one⟩

end GlobalTheory.TameKummer

#print axioms GlobalTheory.TameKummer.frobenius_conj_div_wild_of_card
