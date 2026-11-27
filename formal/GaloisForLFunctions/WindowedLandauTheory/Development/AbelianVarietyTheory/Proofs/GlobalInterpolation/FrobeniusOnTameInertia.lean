import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WildInertiaCriterion
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitPlaceOrder

/-! At a place with residue field of size (p), arithmetic Frobenius
conjugates tame inertia by the (p)-th power. Prime-to-(p) radicals detect
the equality modulo wild inertia. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open ReciprocityTheory.Gal

namespace GlobalTheory.TameKummer

/-- The difference between Frobenius conjugation and the (p)-th power
acts trivially on every prime-to-(p) radical, hence belongs to wild inertia. -/
theorem frobenius_conj_div_wild {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) {p : ℕ} [Fact p.Prime] (hp : A.valuation (p : Ω) < 1)
    {τ φ : G E Ω} (hτ : τ ∈ Ine (F := E) A) (hφ : IsFrob A p φ) :
    let δ := (τ ^ p)⁻¹ * (φ * τ * φ⁻¹)
    δ ∈ Ine (F := E) A ∧ ∀ y : Ω, y ≠ 0 → A.valuation (δ y / y - 1) < 1 := by
  letI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  letI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  letI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  let b := τ ^ p
  let δ := b⁻¹ * (φ * τ * φ⁻¹)
  have hb : b ∈ Ine (F := E) A := pow_mem hτ p
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
  have hphiμ : φ μ = μ ^ p := by
    apply eq_of_pow_eq_one A (natCast_valuation_not_lt_one A hp hpn)
    · rw [← map_pow, hm, map_one]
    · rw [pow_right_comm, hm, one_pow]
    · exact hφ.2 μ (valuation_eq_one_of_pow_eq_one A hn.ne' hm).le
  have hc : (φ * τ * φ⁻¹) y / y = μ ^ p := by
    change φ (τ z) / y = _
    calc
      _ = φ (τ z / z) := by rw [map_div₀, show φ z = y from mul_inv_apply y]
      _ = μ ^ p := by
        rw [ratio_indep A hp hτ hn hpn hy hz]
        exact hphiμ
  have he : b * δ = φ * τ * φ⁻¹ := by dsimp [δ]; group
  have hr := ratio_mul A hp hb hn hpn δ hy
  rw [he, hc, show b y / y = μ ^ p from ratio_npow A hp hτ hn hpn hy p] at hr
  have hunit : δ y / y = 1 :=
    mul_left_cancel₀ (pow_ne_zero p (div_ne_zero ((map_ne_zero τ).mpr hy₀) hy₀))
      (hr.symm.trans (mul_one _).symm)
  exact ⟨y, hy, by rw [hunit, sub_self, map_zero]; exact zero_lt_one⟩

/-- At each designated split place, an arithmetic Frobenius satisfies the tame
conjugation relation in every representation that kills wild inertia. -/
theorem exists_frobenius_conj_of_wild_trivial (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    {M : Type*} [Group M] (ρ : G D.host.E D.nd.Om →* M)
    (hρ : ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
      (∀ y : D.nd.Om, y ≠ 0 → (D.nd.plOm.1 (D.naut.plGw k v)).valuation (s y / y - 1) < 1) →
      ρ s = 1) :
    ∃ φ, ρ (φ * D.ntypes.tg k v * φ⁻¹) = ρ (D.ntypes.tg k v) ^ D.host.g k := by
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  letI := D.nd.acOm
  let w := D.naut.plGw k v
  let A := D.nd.plOm.1 w
  have hw := D.naut.plGw_over k v
  have hp : A.valuation (D.host.g k : D.nd.Om) < 1 := by
    simpa using (D.nd.plOm.2 w (D.host.g k : 𝓞 D.host.E)).mpr hw
  obtain ⟨φ, hφ⟩ := exists_isFrob (D.nd.plOm.2 w)
  rw [(normV_and_notMem_sq_of_split (D.host.g_prime k) (D.nd.g_split k) w hw).1] at hφ
  obtain ⟨hI, hW⟩ := frobenius_conj_div_wild A hp (D.ntypes.tg_mem k v) hφ
  have he := hρ _ hI hW
  change ρ ((D.ntypes.tg k v ^ D.host.g k)⁻¹ * (φ * D.ntypes.tg k v * φ⁻¹)) = 1 at he
  rw [map_mul ρ _ _, map_inv, map_pow] at he
  refine ⟨φ, ?_⟩
  have h := congrArg (fun z => ρ (D.ntypes.tg k v) ^ D.host.g k * z) he
  simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using h

end GlobalTheory.TameKummer
