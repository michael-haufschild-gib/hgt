import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.CurveTensorReceivers

/-!
# Window receivers from the Kloosterman family

The Artin–Schreier–Stepanov estimate for the quadratic twists bounds the squares
of their Hasse–Davenport eigenvalues. Their determinant then forces purity.
The normalized pair defines a curve datum recovering every extension-field trace,
so its window forms are sums of squares. This construction uses the elementary
character-sum estimate and does not assume a monodromy weight theorem.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

open ArithmeticCastelnuovoSeveri
open RHTower.WeilKloosterman

/-- Hasse–Davenport eigenvalues have modulus `√p`, by the twist estimate and determinant. -/
theorem exists_pure_kloosterman_pair {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) {a : ZMod p} (ha : a ≠ 0) :
    ∃ α β : ℂ, α + β = -kloosterman ψ a ∧ α * β = (p : ℂ) ∧
      ‖α‖ = Real.sqrt p ∧ ‖β‖ = Real.sqrt p ∧
      ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
        extKloosterman (E := E) ψ a =
          -(α ^ Module.finrank (ZMod p) E + β ^ Module.finrank (ZMod p) E) := by
  classical
  have hHD : ∀ j : ZMod p, ∃ α β : ℂ, j ≠ 0 →
      α + β = -kloosterman ψ (j ^ 2 * a) ∧ α * β = (p : ℂ) ∧
      ∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
        extKloosterman (E := E) ψ (j ^ 2 * a) =
          -(α ^ Module.finrank (ZMod p) E + β ^ Module.finrank (ZMod p) E) := by
    intro j
    by_cases hj : j = 0
    · exact ⟨0, 0, fun h => absurd hj h⟩
    · obtain ⟨α, β, hs, hd, he⟩ := hasseDavenport ψ (j ^ 2 * a) hψ
        (mul_ne_zero (pow_ne_zero 2 hj) ha)
      exact ⟨α, β, fun _ => ⟨by convert hs, by simpa only [ZMod.card] using hd,
        fun E _ _ _ => he E⟩⟩
  choose α β hαβ using hHD
  have hbound := power_sums_bound hp2 ψ hψ ha α β
    (fun j hj E _ _ _ => (hαβ j (Finset.ne_of_mem_erase hj)).2.2 E)
  let I := (univ.erase (0 : ZMod p)) ×ˢ (univ : Finset Bool)
  let z : ZMod p × Bool → ℂ := fun i => if i.2 then α i.1 ^ 2 else β i.1 ^ 2
  have hz (m : ℕ) : ∑ i ∈ I, z i ^ m =
      ∑ j ∈ univ.erase (0 : ZMod p), ((α j ^ 2) ^ m + (β j ^ 2) ^ m) := by
    rw [Finset.sum_product]
    exact sum_congr rfl fun j _ => by simp [z]
  have hle := norm_le_of_power_sums_bound I z (m0 := 3) (Nat.cast_nonneg p)
    (fun m hm => by rw [hz]; exact hbound m hm)
  have h1 : (1 : ZMod p) ∈ univ.erase (0 : ZMod p) :=
    mem_erase.mpr ⟨one_ne_zero, mem_univ _⟩
  have hα := hle (1, true) (mem_product.mpr ⟨h1, mem_univ _⟩)
  have hβ := hle (1, false) (mem_product.mpr ⟨h1, mem_univ _⟩)
  simp only [z, if_true, Bool.false_eq_true, if_false, norm_pow] at hα hβ
  have hαle := Real.le_sqrt_of_sq_le hα
  have hβle := Real.le_sqrt_of_sq_le hβ
  have hd : α 1 * β 1 = (p : ℂ) := (hαβ 1 one_ne_zero).2.1
  have hprod : ‖α 1‖ * ‖β 1‖ = (p : ℝ) := by
    simpa only [norm_mul, Complex.norm_natCast] using congrArg norm hd
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr := Real.sqrt_pos.mpr hp0
  have hs := Real.sq_sqrt hp0.le
  have hαeq : ‖α 1‖ = Real.sqrt p := le_antisymm hαle (by
    have hl := mul_le_mul_of_nonneg_left hβle (norm_nonneg (α 1))
    nlinarith only [hl, hprod, hs, hr])
  have hβeq : ‖β 1‖ = Real.sqrt p := le_antisymm hβle (by
    have hl := mul_le_mul_of_nonneg_right hαle (norm_nonneg (β 1))
    nlinarith only [hl, hprod, hs, hr])
  refine ⟨α 1, β 1, ?_, hd, hαeq, hβeq, ?_⟩
  · simpa only [one_pow, one_mul] using (hαβ 1 one_ne_zero).1
  · intro E _ _ _
    simpa only [one_pow, one_mul] using (hαβ 1 one_ne_zero).2.2 E

/-- A unit complex number and its conjugate form a pure reciprocal curve datum. -/
def conjugatePairDatum (q : ℝ) (hq : 1 < q) (z : ℂ) (hz : ‖z‖ = 1) :
    CurveDatum (Fin 2) where
  q := q
  one_lt_q := hq
  β := ![z, starRingEnd ℂ z]
  conjPerm := Equiv.swap 0 1
  β_conjPerm := by intro i; fin_cases i <;> simp
  fePerm := Equiv.swap 0 1
  β_fePerm := by
    intro i
    fin_cases i <;> simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, mul_comm]

theorem conjugatePairDatum_pure (q : ℝ) (hq : 1 < q) (z : ℂ) (hz : ‖z‖ = 1)
    (i : Fin 2) : ‖(conjugatePairDatum q hq z hz).β i‖ = 1 := by
  fin_cases i <;> simp [conjugatePairDatum, hz]

/-- Every Kloosterman fibre over an odd prime field has a pure window receiver,
with its traces identified over every finite extension. -/
theorem exists_kloosterman_curve_receiver {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) {a : ZMod p} (ha : a ≠ 0) :
    ∃ D : CurveDatum (Fin 2), D.q = p ∧ (∀ i, ‖D.β i‖ = 1) ∧
      (∀ (E : Type) [Field E] [Fintype E] [Algebra (ZMod p) E],
        extKloosterman (E := E) ψ a =
          -((Real.sqrt p : ℂ) ^ Module.finrank (ZMod p) E) *
            (D.trace (Module.finrank (ZMod p) E) : ℂ)) ∧
      ∀ (S : Finset ℕ) (e : ℕ → ℝ), 0 ≤ D.toeplitz S e := by
  obtain ⟨α, β, _, hd, hα, _, he⟩ := exists_pure_kloosterman_pair hp2 ψ hψ ha
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hr0 : (Real.sqrt p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  let z : ℂ := α / (Real.sqrt p : ℂ)
  have hz : ‖z‖ = 1 := by
    dsimp only [z]
    rw [norm_div, hα, Complex.norm_real, Real.norm_of_nonneg hr.le, div_self hr.ne']
  have hαz : α = (Real.sqrt p : ℂ) * z := by
    dsimp only [z]
    exact (mul_div_cancel₀ α hr0).symm
  have hβz : β = (Real.sqrt p : ℂ) * starRingEnd ℂ z := by
    apply mul_left_cancel₀ (norm_ne_zero_iff.mp (by rw [hα]; exact hr.ne'))
    rw [hd, hαz]
    calc (p : ℂ) = ((Real.sqrt p : ℂ) ^ 2) * (z * starRingEnd ℂ z) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
          simp only [one_pow, Complex.ofReal_one, mul_one]
          exact_mod_cast (Real.sq_sqrt hp0.le).symm
      _ = _ := by ring
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  let D := conjugatePairDatum (p : ℝ) hp1 z hz
  have hU : ∀ i, ‖D.β i‖ = 1 := conjugatePairDatum_pure _ _ _ _
  have hpower (n : ℕ) : D.powerSum n = z ^ n + (starRingEnd ℂ z) ^ n := by
    simp [D, conjugatePairDatum, CurveDatum.powerSum]
  refine ⟨D, rfl, hU, ?_, ?_⟩
  · intro E _ _ _
    rw [he E, ← D.powerSum_eq_trace, hpower]
    rw [hαz, hβz, mul_pow, mul_pow]
    ring
  · intro S e
    rw [D.toeplitz_eq_sum_normSq hU]
    exact sum_nonneg fun i _ => sq_nonneg _

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
