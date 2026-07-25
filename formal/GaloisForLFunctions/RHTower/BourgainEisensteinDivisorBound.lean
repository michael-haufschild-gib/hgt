/-
# Subpolynomial divisor bound in the Eisenstein integers

This is the Eisenstein analogue of `DivisorBound.lean`.  For every
`ε > 0`, the number of normalized-factor submultisets of a nonzero
Eisenstein integer `z` is `Oε(N(z)^ε)`.

The proof is elementary.  Each irreducible factor has integral norm at
least two.  The factor `(a+1)` contributed by multiplicity `a` is absorbed
by `N(p)^{εa}`.  The auxiliary constant differs from one only for
irreducibles of bounded norm, and `BourgainEisensteinSmallNorm` places all
of those in one fixed finite box.
-/
import GaloisForLFunctions.RHTower.BourgainEisensteinSmallNorm

namespace RHTower

open BourgainEisensteinInt

noncomputable section

local instance instEisensteinNormalizationMonoidBound :
    NormalizationMonoid BourgainEisensteinInt :=
  UniqueFactorizationMonoid.normalizationMonoid

/-- Per-factor constant in the Eisenstein divisor bound. -/
noncomputable def eisensteinDvbConst
    (ε : ℝ) (q : BourgainEisensteinInt) : ℝ :=
  max 1 (2 / ((norm q : ℝ) ^ ε - 1))

theorem one_le_eisensteinDvbConst
    (ε : ℝ) (q : BourgainEisensteinInt) :
    1 ≤ eisensteinDvbConst ε q :=
  le_max_left _ _

theorem zero_lt_eisensteinDvbConst
    (ε : ℝ) (q : BourgainEisensteinInt) :
    0 < eisensteinDvbConst ε q :=
  lt_of_lt_of_le one_pos (one_le_eisensteinDvbConst ε q)

theorem one_lt_eisensteinNorm_rpow
    {q : BourgainEisensteinInt} (hq : Irreducible q)
    {ε : ℝ} (hε : 0 < ε) :
    1 < (norm q : ℝ) ^ ε := by
  have hnorm : (1 : ℝ) < norm q := by
    exact_mod_cast two_le_norm_of_irreducible hq
  calc
    (1 : ℝ) = (1 : ℝ) ^ ε := (Real.one_rpow ε).symm
    _ < (norm q : ℝ) ^ ε :=
      Real.rpow_lt_rpow zero_le_one hnorm hε

/-- Commutation of a natural power with a positive real power. -/
theorem eisenstein_rpow_pow_comm
    (q : BourgainEisensteinInt) (a : ℕ) (ε : ℝ) :
    ((norm q : ℝ) ^ ε) ^ a =
      ((norm q : ℝ) ^ (a : ℝ)) ^ ε := by
  have hnorm : (0 : ℝ) ≤ norm q := by
    exact_mod_cast norm_nonneg q
  rw [← Real.rpow_mul_natCast hnorm ε a,
    ← Real.rpow_mul hnorm, mul_comm]

/-- Per-irreducible multiplicity bound. -/
theorem succ_eisensteinFactorization_le
    {q : BourgainEisensteinInt} (hq : Irreducible q)
    {ε : ℝ} (hε : 0 < ε) (a : ℕ) :
    (a + 1 : ℝ) ≤
      eisensteinDvbConst ε q *
        ((norm q : ℝ) ^ (a : ℝ)) ^ ε := by
  have hbase := succ_le_const_mul_pow
    (one_lt_eisensteinNorm_rpow hq hε) a
  rwa [eisenstein_rpow_pow_comm q a ε,
    ← eisensteinDvbConst] at hbase

/-- **Eisenstein divisor bound for normalized-factor submultisets.** -/
theorem eisensteinSubmultisetDivisorCount_le_const_mul_rpow
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ z : BourgainEisensteinInt, z ≠ 0 →
        (eisensteinSubmultisetDivisorCount z : ℝ) ≤
          C * (norm z : ℝ) ^ ε := by
  classical
  set M : ℕ := ⌊(3 : ℝ) ^ (1 / ε)⌋₊ + 1 with hM
  set S : Finset BourgainEisensteinInt :=
    bourgainEisensteinBox M with hS
  refine ⟨∏ q ∈ S, eisensteinDvbConst ε q,
    Finset.prod_pos fun q _ => zero_lt_eisensteinDvbConst ε q, ?_⟩
  intro z hz
  let F : Multiset BourgainEisensteinInt :=
    UniqueFactorizationMonoid.normalizedFactors z
  let P : Finset BourgainEisensteinInt := F.toFinset
  let T : Finset BourgainEisensteinInt :=
    P.filter fun q => (norm q : ℝ) ^ ε < 3
  have hMone : 1 ≤ M := by
    rw [hM]
    omega
  have hTS : T ⊆ S := by
    intro q hqT
    simp only [T, Finset.mem_filter] at hqT
    obtain ⟨hqP, hlt⟩ := hqT
    have hqF : q ∈ F := by
      simpa [P] using hqP
    have hqirr : Irreducible q :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor q hqF
    have hqnorm :
        (norm q : ℝ) < (3 : ℝ) ^ (1 / ε) := by
      have hnormnonneg : (0 : ℝ) ≤ norm q := by
        exact_mod_cast norm_nonneg q
      have h0 : (0 : ℝ) ≤ (norm q : ℝ) ^ ε :=
        Real.rpow_nonneg hnormnonneg ε
      have hlt' := Real.rpow_lt_rpow h0 hlt
        (by positivity : (0 : ℝ) < 1 / ε)
      rwa [← Real.rpow_mul hnormnonneg,
        mul_one_div, div_self (ne_of_gt hε),
        Real.rpow_one] at hlt'
    have hqMreal : (norm q : ℝ) < (M : ℝ) :=
      lt_of_lt_of_le hqnorm (le_of_lt (by
        rw [hM]
        push_cast
        exact Nat.lt_floor_add_one _))
    have hqMint : norm q < (M : ℤ) := by
      exact_mod_cast hqMreal
    rw [hS]
    exact mem_bourgainEisensteinBox_of_norm_lt hMone hqMint
  have hlarge :
      ∀ q ∈ P, q ∉ T → eisensteinDvbConst ε q = 1 := by
    intro q hqP hqnot
    have h3 : 3 ≤ (norm q : ℝ) ^ ε := by
      by_contra h
      apply hqnot
      simp only [T, Finset.mem_filter]
      exact ⟨hqP, not_le.mp h⟩
    rw [eisensteinDvbConst, max_eq_left]
    rw [div_le_one (by linarith)]
    linarith
  have hcount :
      (eisensteinSubmultisetDivisorCount z : ℝ) =
        ∏ q ∈ P, ((F.count q : ℝ) + 1) := by
    rw [eisensteinSubmultisetDivisorCount_eq_prod]
    simp only [F, P]
    push_cast
    rfl
  have hstep :
      ∏ q ∈ P, ((F.count q : ℝ) + 1) ≤
        ∏ q ∈ P,
          eisensteinDvbConst ε q *
            ((norm q : ℝ) ^ ((F.count q : ℕ) : ℝ)) ^ ε := by
    apply Finset.prod_le_prod
    · intro q _
      positivity
    · intro q hqP
      have hqF : q ∈ F := by
        simpa [P] using hqP
      exact succ_eisensteinFactorization_le
        (UniqueFactorizationMonoid.irreducible_of_normalized_factor q
          (by simpa only [F] using hqF))
        hε _
  have hprodE :
      ∏ q ∈ P, q ^ F.count q = F.prod := by
    simpa only [P] using (Finset.prod_multiset_count F).symm
  have hprodNormInt :
      ∏ q ∈ P, norm q ^ F.count q = norm z := by
    calc
      ∏ q ∈ P, norm q ^ F.count q =
          norm (∏ q ∈ P, q ^ F.count q) := by
        symm
        calc
          norm (∏ q ∈ P, q ^ F.count q) =
              ∏ q ∈ P, norm (q ^ F.count q) := by
            exact map_prod normMonoidHom
              (fun q => q ^ F.count q) P
          _ = ∏ q ∈ P, norm q ^ F.count q := by
            apply Finset.prod_congr rfl
            intro q _
            exact normMonoidHom.map_pow q (F.count q)
      _ = norm F.prod := by rw [hprodE]
      _ = norm z :=
        norm_eq_of_associated
          (UniqueFactorizationMonoid.prod_normalizedFactors hz)
  have hprodNorm :
      ∏ q ∈ P, (norm q : ℝ) ^ ((F.count q : ℕ) : ℝ) =
        (norm z : ℝ) := by
    calc
      ∏ q ∈ P, (norm q : ℝ) ^ ((F.count q : ℕ) : ℝ) =
          ∏ q ∈ P, ((norm q ^ F.count q : ℤ) : ℝ) := by
        apply Finset.prod_congr rfl
        intro q hqP
        rw [Real.rpow_natCast]
        push_cast
        ring
      _ = ((∏ q ∈ P, norm q ^ F.count q : ℤ) : ℝ) := by
        rw [Int.cast_prod]
      _ = (norm z : ℝ) := by rw [hprodNormInt]
  have hconst :
      ∏ q ∈ P, eisensteinDvbConst ε q ≤
        ∏ q ∈ S, eisensteinDvbConst ε q := by
    have hrestrict :
        ∏ q ∈ P, eisensteinDvbConst ε q =
          ∏ q ∈ T, eisensteinDvbConst ε q :=
      (Finset.prod_subset (Finset.filter_subset _ _)
        (fun q hqP hqnot => hlarge q hqP hqnot)).symm
    rw [hrestrict]
    have hsplit := Finset.prod_sdiff
      (f := eisensteinDvbConst ε) hTS
    have hge1 :
        (1 : ℝ) ≤
          ∏ q ∈ S \ T, eisensteinDvbConst ε q := by
      calc
        (1 : ℝ) = ∏ _q ∈ S \ T, (1 : ℝ) := by
          rw [Finset.prod_const_one]
        _ ≤ ∏ q ∈ S \ T, eisensteinDvbConst ε q :=
          Finset.prod_le_prod (fun _ _ => zero_le_one)
            (fun q _ => one_le_eisensteinDvbConst ε q)
    have hTpos :
        (0 : ℝ) ≤ ∏ q ∈ T, eisensteinDvbConst ε q :=
      Finset.prod_nonneg
        (fun q _ => (zero_lt_eisensteinDvbConst ε q).le)
    calc
      ∏ q ∈ T, eisensteinDvbConst ε q ≤
          (∏ q ∈ S \ T, eisensteinDvbConst ε q) *
            ∏ q ∈ T, eisensteinDvbConst ε q :=
        le_mul_of_one_le_left hTpos hge1
      _ = ∏ q ∈ S, eisensteinDvbConst ε q := hsplit
  rw [hcount]
  calc
    ∏ q ∈ P, ((F.count q : ℝ) + 1) ≤
        ∏ q ∈ P,
          eisensteinDvbConst ε q *
            ((norm q : ℝ) ^ ((F.count q : ℕ) : ℝ)) ^ ε :=
      hstep
    _ = (∏ q ∈ P, eisensteinDvbConst ε q) *
          ∏ q ∈ P,
            ((norm q : ℝ) ^ ((F.count q : ℕ) : ℝ)) ^ ε :=
      Finset.prod_mul_distrib
    _ = (∏ q ∈ P, eisensteinDvbConst ε q) *
          (∏ q ∈ P,
            (norm q : ℝ) ^ ((F.count q : ℕ) : ℝ)) ^ ε := by
      rw [Real.finsetProd_rpow _ _
        (fun q _ => by
          have : (0 : ℝ) ≤ norm q := by
            exact_mod_cast norm_nonneg q
          positivity)]
    _ = (∏ q ∈ P, eisensteinDvbConst ε q) *
          (norm z : ℝ) ^ ε := by
      rw [hprodNorm]
    _ ≤ (∏ q ∈ S, eisensteinDvbConst ε q) *
          (norm z : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right hconst
        (Real.rpow_nonneg (by exact_mod_cast norm_nonneg z) ε)

/-- **Eisenstein divisor bound.**  The number of actual divisors, including
unit associates, is `Oε(N(z)^ε)`. -/
theorem card_eisensteinDivisors_le_const_mul_rpow
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : BourgainEisensteinInt) (hz : z ≠ 0),
        (@Fintype.card {x : BourgainEisensteinInt // x ∣ z}
          (UniqueFactorizationMonoid.fintypeSubtypeDvd z hz) : ℝ) ≤
            C * (norm z : ℝ) ^ ε := by
  obtain ⟨C₀, hC₀, hC₀bound⟩ :=
    eisensteinSubmultisetDivisorCount_le_const_mul_rpow hε
  set U : ℝ := (Fintype.card BourgainEisensteinIntˣ : ℝ) with hUdef
  have hU : 0 < U := by
    rw [hUdef]
    exact_mod_cast
      (Fintype.card_pos_iff.mpr
        (show Nonempty BourgainEisensteinIntˣ from inferInstance))
  refine ⟨U * C₀, mul_pos hU hC₀, ?_⟩
  intro z hz
  have hcardNat :=
    card_eisensteinDivisors_le_units_mul_submultisets z hz
  have hcard :
      (@Fintype.card {x : BourgainEisensteinInt // x ∣ z}
          (UniqueFactorizationMonoid.fintypeSubtypeDvd z hz) : ℝ) ≤
        U * eisensteinSubmultisetDivisorCount z := by
    rw [hUdef]
    exact_mod_cast hcardNat
  calc
    (@Fintype.card {x : BourgainEisensteinInt // x ∣ z}
        (UniqueFactorizationMonoid.fintypeSubtypeDvd z hz) : ℝ) ≤
        U * eisensteinSubmultisetDivisorCount z := hcard
    _ ≤ U * (C₀ * (norm z : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (hC₀bound z hz) hU.le
    _ = (U * C₀) * (norm z : ℝ) ^ ε := by ring

end

end RHTower
