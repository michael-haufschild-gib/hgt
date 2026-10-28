import GaloisForLFunctions.ArtinMertens.TheDegreeOnePrimesCarryTheMertensSum

/-!
# The degree-one primes of a fixed field count the cosets fixed by Frobenius

Let `G` be a Galois group of a number field `L` over `ℚ`, `H ≤ G` and `F = L^H`. For a prime `p`
unramified in `L` and an arithmetic Frobenius `σ` at a prime `𝔓 | p`,
`|H| · #{𝔮 ⊂ 𝓞_F : N𝔮 = p} = #{g ∈ G : g⁻¹σg ∈ H}` (`card_mul_degreeOneCount_eq`): the number of
degree-one primes of `F` over `p` is the permutation character `π_H(σ)` of `G` on `G/H`.

* **Frobenius generates the decomposition group** (`stabilizer_le_zpowers`): with trivial inertia,
  `D_𝔓 → Gal(k_𝔓/k_p)` is injective and sends `σ` to `x ↦ x^{#k_p}`, which generates.
* **Residue degree as an index** (`inertiaDeg_eq_relIndex`): for `𝔓 | 𝔮 | p` with `𝔓` unramified,
  `f(𝔮|p) = [D_𝔓 : D_𝔓 ∩ H]`, from `|D_𝔓| = f(𝔓|p)`, `|D_𝔓 ∩ H| = f(𝔓|𝔮)` and the tower law.
  Hence `σ_𝔓 ∈ H ⟺ D_𝔓 ≤ H ⟺ f(𝔮|p) = 1 ⟺ N𝔮 = p` (`frob_mem_iff_absNorm_eq`).
* **The fibres are cosets** (`mem_coset_iff_under_eq`): if `N𝔮 = p` and `τ𝔓 | 𝔮`, the `g` with
  `g⁻¹𝔓 | 𝔮` form the coset `τ⁻¹H`, by transitivity of `H` on the primes over `𝔮` and `D_{τ𝔓} ≤ H`.
-/

noncomputable section

open NumberField Ideal MulAction Finset
open scoped Pointwise Classical

namespace GaloisForLFunctions.ArtinMertens

attribute [local instance] Ideal.Quotient.field

section Frobenius

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- **Frobenius generates the unramified decomposition group**: if the inertia group of `P` is
trivial, the stabilizer of `P` consists of powers of any arithmetic Frobenius `σ` at `P`. -/
theorem stabilizer_le_zpowers (p : Ideal A) [p.IsMaximal] [Finite (A ⧸ p)] (P : Ideal B)
    [P.IsMaximal] [P.LiesOver p] [Finite (B ⧸ P)] {σ : G} (hσ : IsArithFrobAt A σ P)
    (hI : P.inertia G = ⊥) :
    stabilizer G P ≤ Subgroup.zpowers σ := by
  cases nonempty_fintype (A ⧸ p)
  have hσP : σ ∈ stabilizer G P := hσ.mem_stabilizer
  -- `σ` acts on `B/P` as `x ↦ x^{#(A/p)}`
  have hφσ : Quotient.stabilizerHom P p G ⟨σ, hσP⟩ =
      FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ p) (B ⧸ P) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hq : Nat.card (A ⧸ P.under A) = Fintype.card (A ⧸ p) := by
      rw [← P.over_def p, Nat.card_eq_fintype_card]
    change Ideal.Quotient.mk P (σ • x) = Ideal.Quotient.mk P x ^ Fintype.card (A ⧸ p)
    rw [← hq, ← map_pow]
    exact Ideal.Quotient.eq.mpr (hσ x)
  intro g hg
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (A ⧸ p) (B ⧸ P)).2
    (Quotient.stabilizerHom P p G ⟨g, hg⟩)
  have hn' : FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ p) (B ⧸ P) ^ n.1 =
      Quotient.stabilizerHom P p G ⟨g, hg⟩ := hn
  have hker : (⟨g, hg⟩ * (⟨σ, hσP⟩ ^ n.1)⁻¹ : stabilizer G P) ∈
      (Quotient.stabilizerHom P p G).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hφσ, ← hn', mul_inv_cancel]
  rw [Quotient.ker_stabilizerHom] at hker
  have hg' : g * (σ ^ n.1)⁻¹ ∈ P.inertia G := hker
  rw [hI, Subgroup.mem_bot, mul_inv_eq_one] at hg'
  rw [hg']
  exact Subgroup.npow_mem_zpowers σ n.1

end Frobenius

section FixedField

variable (L : Type*) [Field L] [NumberField L] {G : Type*} [Group G] [Fintype G]
  [MulSemiringAction G L] [IsGaloisGroup G ℚ L] (H : Subgroup G)

/-- The fixed field `L^H`. -/
abbrev invariantField : IntermediateField ℚ L := FixedPoints.intermediateField H

instance : IsGaloisGroup H (𝓞 (invariantField L H)) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing H _ _ (invariantField L H) L

variable {L H}

/-- **The residue degree in `L^H` is an index**: if `𝔓 | 𝔮 | p` and `𝔓` has trivial inertia, then
`f(𝔮|p) = [D_𝔓 : D_𝔓 ∩ H]`. -/
theorem inertiaDeg_eq_relIndex (p : Ideal ℤ) [p.IsPrime] (Q : Ideal (𝓞 (invariantField L H)))
    [Q.IsPrime] [Q.LiesOver p] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver Q]
    (hI : P.inertia G = ⊥) :
    Q.inertiaDeg ℤ = H.relIndex (stabilizer G P) := by
  have : P.LiesOver p := LiesOver.trans P Q p
  have hIH : P.inertia H = ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    have h' : (h : G) ∈ P.inertia G := hh
    rw [hI, Subgroup.mem_bot] at h'
    exact Subgroup.mem_bot.mpr (Subtype.ext h')
  -- `|D_𝔓| = f(𝔓|p)` and `|D_𝔓 ∩ H| = f(𝔓|𝔮)`
  have hG := card_stabilizer_eq_card_inertia_mul_finrank (G := G) p P
  have hH := card_stabilizer_eq_card_inertia_mul_finrank (G := H) Q P
  rw [hI, Subgroup.card_bot, one_mul] at hG
  rw [hIH, Subgroup.card_bot, one_mul] at hH
  have htower := inertiaDeg_tower (R := ℤ) Q P
  have hcard : Nat.card (stabilizer H P) = Nat.card (H.subgroupOf (stabilizer G P)) :=
    Nat.card_congr
      { toFun := fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩
        invFun := fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hidx : Nat.card (H.subgroupOf (stabilizer G P)) * H.relIndex (stabilizer G P) =
      Nat.card (stabilizer G P) := Subgroup.card_mul_index _
  have hpos : 0 < P.inertiaDeg (𝓞 (invariantField L H)) := by
    rw [← hH]
    exact Nat.card_pos
  have hcard' : P.inertiaDeg (𝓞 (invariantField L H)) =
      Nat.card (H.subgroupOf (stabilizer G P)) := hH.symm.trans hcard
  rw [← hcard', hG, htower] at hidx
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [hidx, mul_comm])

/-- **Degree one means `D_𝔓 ≤ H`** for unramified `𝔓 | 𝔮`. -/
theorem inertiaDeg_eq_one_iff (p : Ideal ℤ) [p.IsPrime] (Q : Ideal (𝓞 (invariantField L H)))
    [Q.IsPrime] [Q.LiesOver p] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver Q]
    (hI : P.inertia G = ⊥) :
    Q.inertiaDeg ℤ = 1 ↔ stabilizer G P ≤ H := by
  rw [inertiaDeg_eq_relIndex p Q P hI, Subgroup.relIndex_eq_one]

theorem absNorm_span_int (p : ℕ) : absNorm (span {(p : ℤ)} : Ideal ℤ) = p := by
  simp

/-- A prime of a characteristic-zero domain over `p` is non-zero. -/
theorem ne_bot_of_liesOver {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (p : ℕ)
    [Fact p.Prime] (P : Ideal R) [P.LiesOver (span {(p : ℤ)})] : P ≠ ⊥ := by
  rintro rfl
  have h := (Ideal.mem_of_liesOver (⊥ : Ideal R) (span {(p : ℤ)}) (p : ℤ)).mp
    (mem_span_singleton_self _)
  simp only [Ideal.mem_bot, map_natCast, Nat.cast_eq_zero] at h
  exact (Fact.out : p.Prime).ne_zero h

omit [Fintype G] [IsGaloisGroup G ℚ L] in
/-- `N𝔮 = p^{f(𝔮|p)}` for `𝔮 | p` in `𝓞_F`. -/
theorem absNorm_eq_pow_inertiaDeg (p : ℕ) [Fact p.Prime] (Q : Ideal (𝓞 (invariantField L H)))
    [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] : absNorm Q = p ^ Q.inertiaDeg ℤ := by
  rw [← absNorm_pow_inertiaDeg (span {(p : ℤ)}) Q, absNorm_span_int]

/-- **Frobenius in `H` means degree one below**: for `𝔓 | p` unramified with arithmetic Frobenius
`τ`, `τ ∈ H ⟺ N(𝔓 ∩ 𝓞_F) = p`. -/
theorem frob_mem_iff_absNorm_eq (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver (span {(p : ℤ)})] (hI : P.inertia G = ⊥) {τ : G} (hτ : IsArithFrobAt ℤ τ P) :
    τ ∈ H ↔ absNorm (P.under (𝓞 (invariantField L H))) = p := by
  have hP0 := ne_bot_of_liesOver p P
  have : Finite (𝓞 L ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  have : P.IsMaximal := Ring.HasFiniteQuotients.maximalOfPrime hP0
  have : (P.under (𝓞 (invariantField L H))).LiesOver (span {(p : ℤ)}) :=
    ⟨by rw [under_under]; exact P.over_def _⟩
  have hcrit := inertiaDeg_eq_one_iff (span {(p : ℤ)}) (P.under (𝓞 (invariantField L H))) P hI
  have : Finite (ℤ ⧸ span {(p : ℤ)}) := Ring.HasFiniteQuotients.finiteQuotient
    (span_singleton_eq_bot.not.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
  rw [absNorm_eq_pow_inertiaDeg p]
  have hp2 := (Fact.out : p.Prime).two_le
  constructor
  · intro hτH
    rw [hcrit.mpr ((stabilizer_le_zpowers (span {(p : ℤ)}) P hτ hI).trans
      (Subgroup.zpowers_le.mpr hτH)),
      pow_one]
  · intro hN
    exact hcrit.mp (Nat.pow_right_injective hp2 (hN.trans (pow_one p).symm)) hτ.mem_stabilizer

/-- **The fibres are cosets**: if `N𝔮 = p` and `τ𝔓₀ | 𝔮`, then `g⁻¹𝔓₀ | 𝔮` exactly when
`τg ∈ H`. -/
theorem mem_coset_iff_under_eq (p : ℕ) [Fact p.Prime] (P₀ : Ideal (𝓞 L)) [P₀.IsPrime]
    [P₀.LiesOver (span {(p : ℤ)})]
    (hunr : ∀ P : Ideal (𝓞 L), P.IsPrime → P.LiesOver (span {(p : ℤ)}) → P.inertia G = ⊥)
    (Q : Ideal (𝓞 (invariantField L H))) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    (hQ : Q.inertiaDeg ℤ = 1) (τ : G) [(τ • P₀).LiesOver Q] (g : G) :
    (g⁻¹ • P₀).under (𝓞 (invariantField L H)) = Q ↔ τ * g ∈ H := by
  have hD : stabilizer G (τ • P₀) ≤ H :=
    (inertiaDeg_eq_one_iff (span {(p : ℤ)}) Q (τ • P₀)
      (hunr _ inferInstance inferInstance)).mp hQ
  constructor
  · intro hg
    have : (g⁻¹ • P₀).LiesOver Q := ⟨hg.symm⟩
    obtain ⟨h, hh⟩ := exists_smul_eq_of_isGaloisGroup Q (τ • P₀) (g⁻¹ • P₀) H
    have hh' : (h : G) • τ • P₀ = g⁻¹ • P₀ := hh
    -- `h⁻¹ g⁻¹ τ⁻¹` fixes `τ𝔓₀`, so lies in `D_{τ𝔓₀} ≤ H`
    have hst : (h : G)⁻¹ * g⁻¹ * τ⁻¹ ∈ stabilizer G (τ • P₀) := by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, ← hh', inv_smul_smul]
    have h1 := H.mul_mem h.2 (hD hst)
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at h1
    have h2 := H.inv_mem h1
    rwa [mul_inv_rev, inv_inv, inv_inv] at h2
  · intro hg
    have key := under_smul (𝓞 (invariantField L H)) (τ • P₀) ((⟨τ * g, hg⟩ : H)⁻¹)
    have hgP : g⁻¹ • P₀ = (τ * g)⁻¹ • τ • P₀ := by rw [mul_inv_rev, mul_smul, inv_smul_smul]
    rw [hgP]
    exact key.trans ((τ • P₀).over_def Q).symm

/-- **Degree-one primes of `L^H` count the cosets fixed by Frobenius**: for `p` unramified in `L`
and an arithmetic Frobenius `σ` at `𝔓₀ | p`, `|H| · n_F(p) = #{g ∈ G : g⁻¹σg ∈ H}`. -/
theorem card_mul_degreeOneCount_eq (p : ℕ) [Fact p.Prime] (P₀ : Ideal (𝓞 L)) [P₀.IsPrime]
    [P₀.LiesOver (span {(p : ℤ)})]
    (hunr : ∀ P : Ideal (𝓞 L), P.IsPrime → P.LiesOver (span {(p : ℤ)}) → P.inertia G = ⊥)
    {σ : G} (hσ : IsArithFrobAt ℤ σ P₀) :
    Nat.card H * degreeOneCount (invariantField L H) p =
      (univ.filter fun g : G => g⁻¹ * σ * g ∈ H).card := by
  -- `g⁻¹σg` is a Frobenius at `g⁻¹𝔓₀`
  have hstep : ∀ g : G, g⁻¹ * σ * g ∈ H ↔
      absNorm ((g⁻¹ • P₀).under (𝓞 (invariantField L H))) = p := fun g => by
    have hτ := hσ.conj g⁻¹
    rw [inv_inv] at hτ
    exact frob_mem_iff_absNorm_eq p (g⁻¹ • P₀) (hunr _ inferInstance inferInstance) hτ
  rw [filter_congr fun g _ => hstep g]
  have hmaps : ∀ g ∈ univ.filter (fun g : G =>
      absNorm ((g⁻¹ • P₀).under (𝓞 (invariantField L H))) = p),
      (g⁻¹ • P₀).under (𝓞 (invariantField L H)) ∈ (idealsLe (invariantField L H) p).filter
        fun Q => Q.IsPrime ∧ absNorm Q = p := by
    intro g hg
    rw [mem_filter] at hg ⊢
    refine ⟨mem_idealsLe.mpr ⟨fun h0 => ?_, hg.2.le⟩, inferInstance, hg.2⟩
    rw [h0, absNorm_bot] at hg
    exact (Fact.out : p.Prime).ne_zero hg.2.symm
  rw [card_eq_sum_card_fiberwise hmaps, degreeOneCount, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun Q hQ => ?_
  rw [mem_filter] at hQ
  obtain ⟨-, hQp, hQN⟩ := hQ
  -- `𝔮` lies over `p` with degree one
  have hQ1 : Q.LiesOver (span {(p : ℤ)}) := by
    refine (Ideal.liesOver_span_iff hQp.ne_top (Nat.prime_iff_prime_int.mp Fact.out)).mpr ?_
    have := absNorm_mem Q
    rwa [hQN, ← map_natCast (algebraMap ℤ (𝓞 (invariantField L H)))] at this
  have hf : Q.inertiaDeg ℤ = 1 := by
    have h := absNorm_eq_pow_inertiaDeg p Q
    rw [hQN] at h
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (h.symm.trans (pow_one p).symm)
  -- a prime `τ𝔓₀` above `𝔮`
  obtain ⟨⟨P₁, hP₁, hP₁Q⟩⟩ := (inferInstance : Nonempty (primesOver Q (𝓞 L)))
  have : P₁.LiesOver (span {(p : ℤ)}) := LiesOver.trans P₁ Q _
  obtain ⟨τ, rfl⟩ := exists_smul_eq_of_isGaloisGroup (span {(p : ℤ)}) P₀ P₁ G
  have hfib : (univ.filter fun g : G =>
      absNorm ((g⁻¹ • P₀).under (𝓞 (invariantField L H))) = p).filter
        (fun g => (g⁻¹ • P₀).under (𝓞 (invariantField L H)) = Q) =
      univ.filter fun g : G => τ * g ∈ H := by
    ext g
    simp only [mem_filter, mem_univ, true_and]
    rw [← mem_coset_iff_under_eq p P₀ hunr Q hf τ g]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by rw [h, hQN], h⟩
  rw [hfib, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr
    { toFun := fun h => ⟨τ⁻¹ * h.1, by simp⟩
      invFun := fun g => ⟨τ * g.1, (mem_filter.mp g.2).2⟩
      left_inv := fun h => by simp
      right_inv := fun g => by simp }

end FixedField

end GaloisForLFunctions.ArtinMertens
