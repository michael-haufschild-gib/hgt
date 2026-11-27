import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WildInertiaCriterion

/-! A finite collection of prime-to-characteristic radical characters
detects any finite quotient of inertia that is trivial on wild inertia. -/

noncomputable section

open NumberField WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameKummer

/-- An open set containing wild inertia contains every inertia element raised
to one common exponent prime to the residue characteristic. -/
theorem exists_primeTo_pow_mem_of_wild_mem {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    {p : ℕ} [Fact p.Prime] (hp : A.valuation (p : Ω) < 1)
    {U : Set (G E Ω)} (hU : IsOpen U)
    (hW : ∀ σ ∈ Ine (F := E) A, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → σ ∈ U) :
    ∃ M : ℕ, 0 < M ∧ p.Coprime M ∧ ∀ σ ∈ Ine (F := E) A, σ ^ M ∈ U := by
  classical
  letI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  letI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  letI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  letI : IsGalois E Ω := {}
  let m (d : ℕ) := p ^ (d + 1) - 1
  have hm (d : ℕ) : 0 < m d :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt)
  have hc (d : ℕ) : p.Coprime (m d) := coprime_pow_sub_one (Nat.succ_pos d)
  choose r hr using fun d : ℕ => IsAlgClosed.exists_pow_nat_eq (p : Ω) (hm d)
  let C : Set (G E Ω) := (Ine (F := E) A : Set (G E Ω)) ∩ Uᶜ
  have hC : IsCompact C := ((isClosed_Ine A).inter hU.isClosed_compl).isCompact
  let V (d : ℕ) : Set (G E Ω) := {σ | σ (r d) / r d ≠ 1}
  have hV (d : ℕ) : IsOpen (V d) := isOpen_setOf_apply (r d) (fun z => z / r d ≠ 1)
  have hcover : C ⊆ ⋃ d, V d := by
    intro σ hσ
    by_contra hh
    have hr₁ (d : ℕ) : σ (r d) / r d = 1 := by
      by_contra hne
      exact hh (Set.mem_iUnion.mpr ⟨d, hne⟩)
    have hw := valuation_sub_one_lt_of_trivial_tame A hp hσ.1 (fun d hd => by
      refine ⟨r (d - 1), ?_, ?_⟩
      · simpa only [m, Nat.sub_add_cancel hd] using hr (d - 1)
      · rw [hr₁, sub_self, map_zero]
        exact zero_lt_one)
    exact hσ.2 (hW σ hσ.1 hw)
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover V hV hcover
  let M := ∏ d ∈ s, m d
  refine ⟨M, Finset.prod_pos (fun d _ => hm d), Nat.Coprime.prod_right (fun d _ => hc d), ?_⟩
  intro σ hσ
  by_contra hσU
  obtain ⟨d, hd, hne⟩ := Set.mem_iUnion₂.mp (hs ⟨pow_mem hσ M, hσU⟩)
  change (σ ^ M) (r d) / r d ≠ 1 at hne
  have hp₀ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hrpow : (σ (r d) / r d) ^ m d = 1 := ratio_pow_eq_one σ hp₀ (hr d)
  obtain ⟨j, hj⟩ : m d ∣ M := Finset.dvd_prod_of_mem m hd
  apply hne
  rw [ratio_npow A hp hσ (hm d) (hc d) (hr d), hj, pow_mul, hrpow, one_pow]

end GlobalTheory.TameKummer
