import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumberResidue
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TeichmullerReduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedTypeReduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameKummerSurjectivity
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WildInertiaCriterion

/-! Compatible primitive residue generators determine a tame inertia generator
by compactness along the tower of prime-to-characteristic radical extensions. -/

noncomputable section

open NumberField IsDedekindDomain IsLocalRing
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.CyclotomicNorms WindowedLandauTheory.NormalizedTypes
open ReciprocityTheory.Gal GlobalTheory.GLq GlobalTheory.TeichPlace

namespace GlobalTheory.TameKummer

variable {p : ℕ} [Fact p.Prime]

private theorem pow_sub_one_pos {d : ℕ} (hd : 0 < d) : 0 < p ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)

private theorem gen_norm_of_dvd (L : LabelDatum p) {d e : ℕ}
    (hd : 0 < d) (he : 0 < e) (hde : d ∣ e) :
    (L.gen e) ^ ((p ^ e - 1) / (p ^ d - 1)) = L.gen d := by
  obtain ⟨a, rfl⟩ := hde
  exact L.gen_norm d a hd (Nat.pos_of_mul_pos_left he)

omit [Fact p.Prime] in
private theorem radical_descends {Ω : Type} [Field Ω] {d e : ℕ} (hde : d ∣ e) {r : Ω}
    (hr : r ^ (p ^ e - 1) = (p : Ω)) :
    (r ^ ((p ^ e - 1) / (p ^ d - 1))) ^ (p ^ d - 1) = (p : Ω) := by
  rw [← pow_mul, Nat.div_mul_cancel (Nat.pow_sub_one_dvd_pow_sub_one p hde), hr]

private theorem ratio_descends {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [CharZero Ω] [Algebra E Ω] (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {d e : ℕ} (hd : 0 < d) (hde : d ∣ e)
    {y r : Ω} (hy : y ^ (p ^ d - 1) = (p : Ω)) (hr : r ^ (p ^ e - 1) = (p : Ω)) :
    σ y / y = (σ r / r) ^ ((p ^ e - 1) / (p ^ d - 1)) := by
  rw [ratio_indep A hp hσ (pow_sub_one_pos (p := p) hd) (coprime_pow_sub_one hd)
    (radical_descends hde hr) hy, map_pow, div_pow]

private theorem redThrough_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    (κ : ResidueField A ≃+* Fbar p) : redThrough A κ 1 = 1 := by
  rw [redThrough, dif_pos (one_mem A)]
  change κ (residue A 1) = 1
  rw [map_one, map_one]

/-- A prescribed system of finite-field generators is realized by a single
absolute inertia automorphism when the rational residue prime has order one. -/
theorem exists_coupled_tame_generator {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)) (hA : IsPlaceOver A v)
    (hp : (p : 𝓞 E) ∈ v.asIdeal) (hsq : (p : 𝓞 E) ∉ v.asIdeal ^ 2)
    (L : LabelDatum p) :
    ∃ κ : ResidueField A ≃+* Fbar p, ∃ σ ∈ Ine (F := E) A,
      TameGenAt A σ ∧ TameCoupled A κ σ L.gen := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  letI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  letI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  letI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  letI : IsGalois E Ω := {}
  have hpv : A.valuation (p : Ω) < 1 := by simpa using (hA (p : 𝓞 E)).mpr hp
  have hp₀ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨κ⟩ := nonempty_fbar_residueField_of_valuation A p hpv
  let D (n : ℕ) := (n + 1).factorial
  let N (d : ℕ) := p ^ d - 1
  have hD (n : ℕ) : 0 < D n := Nat.factorial_pos _
  have hN {d : ℕ} (hd : 0 < d) : 0 < N d := pow_sub_one_pos (p := p) hd
  have hcop {d : ℕ} (hd : 0 < d) : p.Coprime (N d) := coprime_pow_sub_one hd
  have hstep (n : ℕ) : D n ∣ D (n + 1) := Nat.factorial_dvd_factorial (Nat.le_succ _)
  have hdiv (d : ℕ) (hd : 0 < d) : d ∣ D d := Nat.dvd_factorial hd (Nat.le_succ _)
  have hroot (n : ℕ) : ∃ r : Ω, r ^ N (D n) = (p : Ω) := IsAlgClosed.exists_pow_nat_eq _ (hN (hD n))
  choose r hr using hroot
  let ratio (n : ℕ) (τ : G E Ω) := τ (r n) / r n
  have hpow (n : ℕ) (τ : G E Ω) : ratio n τ ^ N (D n) = 1 := ratio_pow_eq_one τ hp₀ (hr n)
  have hmem (n : ℕ) (τ : G E Ω) : ratio n τ ∈ A :=
    (A.valuation_le_one_iff _).mp (valuation_eq_one_of_pow_eq_one A (hN (hD n)).ne' (hpow n τ)).le
  have hdown (τ : G E Ω) (hτ : τ ∈ Ine (F := E) A) {d : ℕ} (hd : 0 < d)
      {n : ℕ} (hdD : d ∣ D n) {y : Ω} (hy : y ^ N d = (p : Ω)) :
      τ y / y = ratio n τ ^ (N (D n) / N d) :=
    ratio_descends A hpv hτ hd hdD hy (hr n)
  let T (n : ℕ) : Set (G E Ω) :=
    (Ine (F := E) A : Set (G E Ω)) ∩ {τ | redThrough A κ (ratio n τ) = L.gen (D n)}
  have hclosed (n : ℕ) : IsClosed (T n) :=
    (isClosed_Ine A).inter (isClosed_setOf_apply (r n) (fun x => redThrough A κ (x / r n) = L.gen (D n)))
  obtain ⟨σ, hσ⟩ : (⋂ n, T n).Nonempty := by
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T ?_ ?_ (hclosed 0).isCompact hclosed
    · rintro n τ ⟨hτ, ht⟩
      refine ⟨hτ, ?_⟩
      change redThrough A κ (ratio n τ) = L.gen (D n)
      change redThrough A κ (ratio (n + 1) τ) = L.gen (D (n + 1)) at ht
      rw [show ratio n τ = ratio (n + 1) τ ^ (N (D (n + 1)) / N (D n)) from
          hdown τ hτ (hD n) (hstep n) (hr n), redThrough_pow A κ (hmem (n + 1) τ), ht]
      exact gen_norm_of_dvd L (hD n) (hD (n + 1)) (hstep n)
    · intro n
      have hc : L.gen (D n) ^ N (D n) = 1 := by
        rw [show N (D n) = orderOf (L.gen (D n)) from (L.gen_order _ (hD n)).symm]
        exact pow_orderOf_eq_one _
      obtain ⟨μ, hμ, hμc⟩ := exists_rootOfUnity_lift A κ (hN (hD n)) (hcop (hD n)) hc
      obtain ⟨τ, hτ, hμr⟩ := exists_inertia_mul_of_radical A v hA p hp hsq (hN (hD n))
        (hcop (hD n)) (hr n) hμ
      refine ⟨τ, hτ, ?_⟩
      have hr₀ : r n ≠ 0 := fun h => hp₀ (by simpa [h, (hN (hD n)).ne'] using (hr n).symm)
      change redThrough A κ (τ (r n) / r n) = L.gen (D n)
      rw [hμr, mul_div_cancel_right₀ _ hr₀, hμc]
  simp only [Set.mem_iInter] at hσ
  have hσI : σ ∈ Ine (F := E) A := (hσ 0).1
  have hσv (n : ℕ) : redThrough A κ (ratio n σ) = L.gen (D n) := (hσ n).2
  have hprim (n : ℕ) : IsPrimitiveRoot (ratio n σ) (N (D n)) := by
    have hgen : IsPrimitiveRoot (L.gen (D n)) (N (D n)) := by
      rw [show N (D n) = orderOf (L.gen (D n)) from (L.gen_order _ (hD n)).symm]
      exact IsPrimitiveRoot.orderOf _
    refine ⟨hpow n σ, fun m hm => hgen.dvd_of_pow_eq_one m ?_⟩
    rw [← hσv n, ← redThrough_pow A κ (hmem n σ), hm, redThrough_one]
  refine ⟨κ, σ, hσI, ⟨hσI, ?_⟩, ?_⟩
  · intro τ hτ
    let Z : Set (G E Ω) := closure (Subgroup.zpowers σ : Set (G E Ω))
    have hZI : Z ⊆ Ine (F := E) A := closure_minimal (fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact zpow_mem hσI k) (isClosed_Ine A)
    let U (n : ℕ) : Set (G E Ω) := Z ∩ {h | ratio n h = ratio n τ}
    have hU (n : ℕ) : IsClosed (U n) :=
      isClosed_closure.inter (isClosed_setOf_apply (r n) (fun x => x / r n = ratio n τ))
    obtain ⟨h, hh⟩ : (⋂ n, U n).Nonempty := by
      refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed U ?_ ?_ (hU 0).isCompact hU
      · rintro n x ⟨hx, he⟩
        refine ⟨hx, ?_⟩
        change ratio n x = ratio n τ
        change ratio (n + 1) x = ratio (n + 1) τ at he
        rw [show ratio n x = ratio (n + 1) x ^ (N (D (n + 1)) / N (D n)) from
          hdown x (hZI hx) (hD n) (hstep n) (hr n),
          show ratio n τ = ratio (n + 1) τ ^ (N (D (n + 1)) / N (D n)) from
          hdown τ hτ (hD n) (hstep n) (hr n), he]
      · intro n
        letI : NeZero (N (D n)) := ⟨(hN (hD n)).ne'⟩
        obtain ⟨j, -, hj⟩ := (hprim n).eq_pow_of_pow_eq_one (hpow n τ)
        refine ⟨σ ^ j, subset_closure (Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), by simp⟩), ?_⟩
        change (σ ^ j) (r n) / r n = ratio n τ
        exact (ratio_npow A hpv hσI (hN (hD n)) (hcop (hD n)) (hr n) j).trans hj
    simp only [Set.mem_iInter] at hh
    have hhZ : h ∈ Z := (hh 0).1
    have hhI := hZI hhZ
    have hρI : h⁻¹ * τ ∈ Ine (F := E) A := mul_mem (inv_mem hhI) hτ
    have hρ (n : ℕ) : ratio n (h⁻¹ * τ) = 1 := by
      have e := ratio_mul A hpv hhI (hN (hD n)) (hcop (hD n)) (h⁻¹ * τ) (hr n)
      rw [mul_inv_cancel_left] at e
      change ratio n τ = ratio n h * ratio n (h⁻¹ * τ) at e
      rw [← (hh n).2] at e
      have hne : ratio n h ≠ 0 := by
        intro hz
        have hpw := hpow n h
        rw [hz, zero_pow (hN (hD n)).ne'] at hpw
        exact zero_ne_one hpw
      exact (mul_eq_left₀ hne).mp e.symm
    have hWild := valuation_sub_one_lt_of_trivial_tame A hpv hρI (by
      intro d hd
      have hroot := radical_descends (hdiv d hd) (hr d)
      refine ⟨r d ^ (N (D d) / N d), hroot, ?_⟩
      rw [hdown _ hρI hd (hdiv d hd) hroot, hρ, one_pow, sub_self, map_zero]
      exact zero_lt_one)
    let C : Subgroup (G E Ω) := Subgroup.closure
      (insert σ {π : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (π y / y - 1) < 1})
    have hzC : h ∈ C.topologicalClosure := closure_mono (fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _) : σ ∈ C) k) hhZ
    have hρC : h⁻¹ * τ ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem _ hWild)
    have hhC := C.topologicalClosure.mul_mem hzC (C.le_topologicalClosure hρC)
    rwa [mul_inv_cancel_left] at hhC
  · intro d hd y hy
    rw [hdown σ hσI hd (hdiv d hd) hy, redThrough_pow A κ (hmem d σ), hσv]
    exact gen_norm_of_dvd L hd (hD d) (hdiv d hd)

end GlobalTheory.TameKummer
