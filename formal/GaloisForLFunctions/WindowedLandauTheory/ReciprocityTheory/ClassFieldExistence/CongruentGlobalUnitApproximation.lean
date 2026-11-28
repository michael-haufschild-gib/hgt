import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.CongruentGlobalValuations
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ChevalleyUnitPowers

/-! Chevalley's congruence theorem rules out a nontrivial local unit
admitting principal approximations of arbitrary congruence level. -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace GlobalTheory.Reciprocity

variable {E : Type} [Field E] [NumberField E]

private theorem exists_unitPower_dvd_sub_one {R : Type*} [CommRing R] (g : R)
    [Finite (R ⧸ Ideal.span {g})] :
    ∃ m : ℕ, 0 < m ∧ ∀ ε : Rˣ, g ∣ (ε : R) ^ m - 1 := by
  let A := R ⧸ Ideal.span {g}
  let f : R →+* A := Ideal.Quotient.mk _
  letI : Finite Aˣ := Finite.of_injective Units.val Units.val_injective
  refine ⟨Nat.card Aˣ, Nat.card_pos, fun ε => ?_⟩
  have h := pow_card_eq_one' (x := Units.map f.toMonoidHom ε)
  have h' : f ((ε : R) ^ Nat.card Aˣ) = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Units.val_one, map_pow] using congrArg Units.val h
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change f ((ε : R) ^ Nat.card Aˣ - 1) = 0
  rw [map_sub, h', map_one, sub_self]

private theorem valuation_natCast_eq_one_of_coprime_absNorm (w : HeightOneSpectrum (𝓞 E))
    (a : ℕ) (ha : a.Coprime (Ideal.absNorm w.asIdeal)) : w.valuation E (a : E) = 1 := by
  rw [← map_natCast (algebraMap (𝓞 E) E), valuation_eq_one_iff_notMem]
  intro h
  obtain ⟨s, t, hst⟩ := (Nat.isCoprime_iff_coprime.mpr ha).map (Int.castRingHom (𝓞 E))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hst]
  simp only [eq_intCast, Int.cast_natCast]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left s h)
    (w.asIdeal.mul_mem_left t (Ideal.absNorm_mem _))

private theorem exists_congruent_integerUnit (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) (hx : Valued.v x = 1)
    (hap : HasCongruentGlobalApproximants w x) (a : ℕ)
    (ha : 0 < a) (hwa : w.valuation E (a : E) = 1) (t : w.adicCompletion E)
    (ht : t ≠ 0) (ht' : Valued.v t < 1) :
    ∃ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 ∧
      Valued.v (algebraMap (𝓞 E) (w.adicCompletion E) (u : 𝓞 E) - x) ≤ Valued.v t := by
  obtain ⟨k, hoff, hw⟩ := hap a ha t ht
  have hwk : w.valuation E (k : E) = 1 := by
    rw [← valuedAdicCompletion_eq_valuation', ← hx]
    exact Valuation.map_eq_of_sub_lt _ (hw.trans_lt (by rwa [hx]))
  obtain ⟨u, hu⟩ := exists_integerUnit_of_valuation_eq_one (k : E) (fun v => by
    by_cases h : v = w
    · subst v; exact hwk
    · exact valuation_eq_one_of_ray v a ha k (hoff v h).1 (hoff v h).2) k.ne_zero
  obtain ⟨y, hy⟩ := congruent_integer_of_valuations w a ha hwa k (u : 𝓞 E) hu
    (fun v hv => (hoff v hv).1)
  refine ⟨u, ⟨y, ?_⟩, ?_⟩
  · rw [hy]; ring
  · rwa [IsScalarTower.algebraMap_apply (𝓞 E) E (w.adicCompletion E), hu]

private theorem valued_sub_one_le_of_divisibility (w : HeightOneSpectrum (𝓞 E))
    (u g : 𝓞 E) (h : g ∣ u - 1) :
    Valued.v (algebraMap (𝓞 E) (w.adicCompletion E) u - 1) ≤ w.intValuation g := by
  have hE (z : E) : Valued.v (algebraMap E (w.adicCompletion E) z) = w.valuation E z :=
    valuedAdicCompletion_eq_valuation' w z
  rw [← map_one (algebraMap (𝓞 E) (w.adicCompletion E)), ← map_sub,
    IsScalarTower.algebraMap_apply (𝓞 E) E (w.adicCompletion E), hE, valuation_of_algebraMap]
  obtain ⟨c, hc⟩ := h
  rw [hc, map_mul]
  exact mul_le_of_le_one_right' (w.intValuation_le_one c)

theorem eq_one_of_congruent_global_approximants (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) (hx : Valued.v x = 1)
    (hap : HasCongruentGlobalApproximants w x) : x = 1 := by
  let q := Ideal.absNorm w.asIdeal
  have hq₀ : q ≠ 0 := fun he => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp he)
  have hqmem : (q : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem _
  let γ := w.intValuation (q : 𝓞 E)
  have hγ : γ < 1 := (w.intValuation_lt_one_iff_mem _).mpr hqmem
  have hpowers (n : ℕ) : Valued.v (x - 1) ≤ γ ^ (n + 1) := by
    let g : 𝓞 E := (q : 𝓞 E) ^ (n + 1)
    have hg₀ : g ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hq₀)
    letI : Finite (𝓞 E ⧸ Ideal.span {g}) := by
      apply (Ideal.absNorm_ne_zero_iff _).mp
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hg₀
    obtain ⟨m, hm, hmg⟩ := exists_unitPower_dvd_sub_one g
    obtain ⟨a, ha, hac, hroot⟩ := exists_coprime_congruence_for_unit_powers E m q hm (Nat.pos_of_ne_zero hq₀)
    let t := algebraMap (𝓞 E) (w.adicCompletion E) g
    have ht₀ : t ≠ 0 := by
      change algebraMap (𝓞 E) (w.adicCompletion E) g ≠ 0
      rw [IsScalarTower.algebraMap_apply (𝓞 E) E (w.adicCompletion E),
        map_ne_zero_iff _ (algebraMap E (w.adicCompletion E)).injective]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hg₀
    have hvt : Valued.v t = γ ^ (n + 1) := by
      dsimp only [t]
      have hE (z : E) : Valued.v (algebraMap E (w.adicCompletion E) z) = w.valuation E z :=
        valuedAdicCompletion_eq_valuation' w z
      rw [IsScalarTower.algebraMap_apply (𝓞 E) E (w.adicCompletion E), hE, valuation_of_algebraMap]
      exact map_pow w.intValuation _ _
    have ht₁ : Valued.v t < 1 := by
      rw [hvt]
      exact pow_lt_one₀ zero_le' hγ (Nat.succ_ne_zero n)
    obtain ⟨u, hu, hux⟩ := exists_congruent_integerUnit w x hx hap a ha
      (valuation_natCast_eq_one_of_coprime_absNorm w a hac) t ht₀ ht₁
    obtain ⟨ε, hε⟩ := hroot u hu
    have hg : g ∣ (u : 𝓞 E) - 1 := by
      simpa only [← Units.val_pow_eq_pow_val, hε] using hmg ε
    have hu₁ := valued_sub_one_le_of_divisibility w (u : 𝓞 E) g hg
    have hvg : w.intValuation g = γ ^ (n + 1) := map_pow w.intValuation _ _
    rw [hvg] at hu₁
    rw [hvt] at hux
    have he : x - 1 = (x - algebraMap (𝓞 E) (w.adicCompletion E) (u : 𝓞 E)) +
        (algebraMap (𝓞 E) (w.adicCompletion E) (u : 𝓞 E) - 1) := by ring
    rw [he]
    apply Valuation.map_add_le _ _ hu₁
    rw [← neg_sub, Valuation.map_neg]
    exact hux
  by_contra hne
  have hpos : Valued.v (x - 1) ≠ 0 := (Valuation.ne_zero_iff _).mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hγ (Units.mk0 _ hpos)
  have hs : γ ^ (n + 1) ≤ γ ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right' hγ.le
  exact (not_lt_of_ge ((hpowers n).trans hs)) hn

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.eq_one_of_congruent_global_approximants
