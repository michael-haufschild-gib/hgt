import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import GaloisForLFunctions.HTGeometry.QuotientPowerMonogenic

/-!
# A local uniformiser generates modulo a power

In a Dedekind domain, an element of a nonzero prime `Q` that is not in `Q²` generates `Q` modulo any
power of `Q`: the ideal `(t) + Qᵏ` lies between `Qᵏ` and `Q`, hence divides `Qᵏ`, hence is a power of
`Q`; it is not `⊤` because it is contained in `Q`, and not `Q²` or smaller because it contains `t`.

Consequently the image of `Q` in `B/J` is principal for every `J` with `Qᵏ ≤ J ≤ Q` — in particular
in `B/Qᵏ` and in `B/(Qᵏ + uB)`.  That is the hypothesis the monogenicity criterion needs on the
local factors of the residue algebra.
-/

namespace GaloisForLFunctions.HTGeometry

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

/-- A nonzero prime of a Dedekind domain strictly contains its square. -/
theorem exists_mem_not_mem_sq {Q : Ideal B} (hQ0 : Q ≠ ⊥) (hQT : Q ≠ ⊤) :
    ∃ t ∈ Q, t ∉ Q ^ (2 : ℕ) := by
  obtain ⟨t, htQ, htn⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self Q hQ0 hQT 2 le_rfl)
  exact ⟨t, htQ, htn⟩

/-- **An element of `Q` outside `Q²` generates `Q` modulo any power of `Q`.** -/
theorem span_sup_pow_eq {Q : Ideal B} [hQp : Q.IsPrime] (hQ0 : Q ≠ ⊥) {t : B}
    (ht : t ∈ Q) (ht2 : t ∉ Q ^ (2 : ℕ)) {k : ℕ} (hk : 1 ≤ k) :
    Ideal.span {t} ⊔ Q ^ k = Q := by
  have hprime : Prime Q := Ideal.prime_of_isPrime hQ0 hQp
  have hspan : Ideal.span {t} ≤ Q := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ht
  have hJle : Ideal.span {t} ⊔ Q ^ k ≤ Q :=
    sup_le hspan (Ideal.pow_le_self (by omega))
  have hdvd : (Ideal.span {t} ⊔ Q ^ k) ∣ Q ^ k := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨m, hmk, hassoc⟩ := (dvd_prime_pow hprime k).mp hdvd
  have hJeq : Ideal.span {t} ⊔ Q ^ k = Q ^ m := by
    obtain ⟨u, hu⟩ := hassoc
    have hutop : (u : Ideal B) = 1 := by
      rw [Ideal.isUnit_iff.mp u.isUnit, Ideal.one_eq_top]
    rw [hutop, mul_one] at hu
    exact hu
  have hm1 : 1 ≤ m := by
    by_contra hc
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero, Ideal.one_eq_top] at hJeq
    exact hQp.ne_top (top_le_iff.mp (hJeq ▸ hJle))
  have hm2 : m < 2 := by
    by_contra hc
    have hle : Q ^ m ≤ Q ^ (2 : ℕ) := Ideal.pow_le_pow_right (by omega)
    refine ht2 (hle ?_)
    rw [← hJeq]
    exact Submodule.mem_sup_left (Ideal.mem_span_singleton_self t)
  have : m = 1 := by omega
  rw [hJeq, this, pow_one]

/-- **The image of `Q` in a quotient between `Qᵏ` and `Q` is principal.** -/
theorem map_eq_span_singleton {Q : Ideal B} [Q.IsPrime] (hQ0 : Q ≠ ⊥) {t : B}
    (ht : t ∈ Q) (ht2 : t ∉ Q ^ (2 : ℕ)) {J : Ideal B} (hJQ : J ≤ Q) {k : ℕ} (hk : 1 ≤ k)
    (hkJ : Q ^ k ≤ J) :
    Q.map (Ideal.Quotient.mk J) = Ideal.span {Ideal.Quotient.mk J t} := by
  have hspan : Ideal.span {t} ≤ Q := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact ht
  have hsup : Ideal.span {t} ⊔ J = Q := by
    refine le_antisymm (sup_le hspan hJQ) ?_
    rw [← span_sup_pow_eq hQ0 ht ht2 hk]
    exact sup_le le_sup_left (le_trans hkJ le_sup_right)
  rw [← hsup, Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq, Ideal.map_span,
    Set.image_singleton]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

/-! ## The maximal ideals of a quotient of a Dedekind domain -/

/-- If a maximal ideal is a principal ideal plus its own `n`-th power, its image in the quotient by
that power is principal. -/
theorem map_pow_eq_span_of_sup {R : Type*} [CommRing R] {I : Ideal R} {s : R} {n : ℕ}
    (h : I = Ideal.span {s} ⊔ I ^ n) :
    I.map (Ideal.Quotient.mk (I ^ n)) = Ideal.span {Ideal.Quotient.mk (I ^ n) s} := by
  have h1 : I.map (Ideal.Quotient.mk (I ^ n))
      = (Ideal.span {s} ⊔ I ^ n).map (Ideal.Quotient.mk (I ^ n)) := by rw [← h]
  rw [h1, Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq, Ideal.map_span, Set.image_singleton]

/-- **Every maximal ideal of a quotient of a Dedekind domain is principal modulo its own power.** -/
theorem exists_sup_pow_eq_of_maximal_quotient {B : Type*} [CommRing B] [IsDedekindDomain B]
    {𝔞 : Ideal B} (h𝔞 : 𝔞 ≠ ⊥) (I : Ideal (B ⧸ 𝔞)) [hI : I.IsMaximal] {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : B ⧸ 𝔞, I = Ideal.span {s} ⊔ I ^ n := by
  set Q : Ideal B := I.comap (Ideal.Quotient.mk 𝔞) with hQdef
  haveI hQmax : Q.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have h𝔞Q : 𝔞 ≤ Q := by
    intro x hx
    rw [hQdef, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Submodule.zero_mem _
  have hQ0 : Q ≠ ⊥ := by
    intro hbot
    exact h𝔞 (le_bot_iff.mp (hbot ▸ h𝔞Q))
  obtain ⟨t, htQ, ht2⟩ := exists_mem_not_mem_sq hQ0 hQmax.ne_top
  have hQeq : Ideal.span {t} ⊔ Q ^ n = Q := span_sup_pow_eq hQ0 htQ ht2 hn
  have hmapQ : Q.map (Ideal.Quotient.mk 𝔞) = I :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective I
  refine ⟨Ideal.Quotient.mk 𝔞 t, ?_⟩
  have := congrArg (fun J : Ideal B => J.map (Ideal.Quotient.mk 𝔞)) hQeq
  simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow, hmapQ] at this
  exact this.symm

/-- **A finite-dimensional quotient of a Dedekind domain is generated by one element.** -/
theorem exists_adjoin_eq_top_quotient_dedekind {κ B : Type*} [Field κ] [CharZero κ]
    [CommRing B] [IsDedekindDomain B] {𝔞 : Ideal B} [Algebra κ (B ⧸ 𝔞)]
    [FiniteDimensional κ (B ⧸ 𝔞)] (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ γ : B ⧸ 𝔞, Algebra.adjoin κ ({γ} : Set (B ⧸ 𝔞)) = ⊤ := by
  classical
  haveI hart : IsArtinianRing (B ⧸ 𝔞) := isArtinian_of_tower κ inferInstance
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B ⧸ 𝔞)
  have hle : nilradical (B ⧸ 𝔞) ≤ Ideal.jacobson (⊥ : Ideal (B ⧸ 𝔞)) := fun x hx =>
    Ideal.radical_le_jacobson hx
  have hnil : (nilradical (B ⧸ 𝔞)) ^ (n + 1) = ⊥ := by
    refine le_bot_iff.mp ?_
    calc (nilradical (B ⧸ 𝔞)) ^ (n + 1)
        ≤ (Ideal.jacobson (⊥ : Ideal (B ⧸ 𝔞))) ^ (n + 1) :=
          pow_le_pow_left' hle _
      _ ≤ (Ideal.jacobson (⊥ : Ideal (B ⧸ 𝔞))) ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
      _ = ⊥ := hn
  refine exists_adjoin_eq_top_of_local_factors_principal (n := n + 1) (Nat.succ_pos n) hnil ?_
  intro I
  haveI : I.asIdeal.IsMaximal := I.isMaximal
  obtain ⟨s, hs⟩ := exists_sup_pow_eq_of_maximal_quotient h𝔞 I.asIdeal (n := n + 1)
    (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n))
  exact ⟨Ideal.Quotient.mk (I.asIdeal ^ (n + 1)) s, map_pow_eq_span_of_sup hs⟩

end GaloisForLFunctions.HTGeometry
