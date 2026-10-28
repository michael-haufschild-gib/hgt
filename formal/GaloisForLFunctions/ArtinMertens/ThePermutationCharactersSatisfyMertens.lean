import GaloisForLFunctions.ArtinMertens.TheDegreeOnePrimesOfAFixedFieldCountFixedCosets

/-!
# Mertens' theorem for permutation characters

Let `G` be a Galois group of a number field `L` over `ℚ` and `H ≤ G`. For any choice of arithmetic
Frobenius elements `Frob_p` at the primes `p ∤ disc L`, the permutation character
`π_H(σ) = #{gH : σgH = gH}` satisfies
`Σ_{p ≤ x, p ∤ disc L} π_H(Frob_p) log p/p ∼ log x` (`tendsto_frobMertens_permChar_div_log`).

* **Unramified primes** (`inertia_eq_bot_of_not_dvd_discr`): for `p ∤ disc L` every prime above `p`
  has ramification index `1`, hence trivial inertia group.
* **Frobenius choices exist** (`exists_isFrobeniusChoice`).
* **Permutation character = degree-one count** (`permChar_frob_eq`): `π_H(Frob_p) = n_{L^H}(p)`.
* **Ramified primes are a bounded error** (`degreeOneMertens_sub_frobMertens_le`): they divide
  `disc L ≠ 0`, so their contribution to `Σ_p n_{L^H}(p) log p/p` is bounded.
-/

noncomputable section

open NumberField Ideal MulAction Finset Filter Topology
open scoped Pointwise Classical

namespace GaloisForLFunctions.ArtinMertens

variable (L : Type*) [Field L] [NumberField L] {G : Type*} [Group G] [Fintype G]
  [MulSemiringAction G L] [IsGaloisGroup G ℚ L]

/-- The **permutation character** `π_H(σ) = #{g : g⁻¹σg ∈ H}/|H|`, the number of cosets `gH`
fixed by `σ`. -/
def permChar (H : Subgroup G) (σ : G) : ℝ :=
  ((univ.filter fun g : G => g⁻¹ * σ * g ∈ H).card : ℝ) / Nat.card H

/-- A **Frobenius choice**: at every prime `p ∤ disc L`, `frob p` is an arithmetic Frobenius at some
prime of `𝓞_L` above `p`. -/
def IsFrobeniusChoice (frob : ℕ → G) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ discr L → ∃ P : Ideal (𝓞 L),
    P.IsPrime ∧ P.LiesOver (span {(p : ℤ)}) ∧ IsArithFrobAt ℤ (frob p) P

/-- The **Frobenius–Mertens sum** `Σ_{p ≤ x, p ∤ disc L} φ(Frob_p) log p/p`. -/
def frobMertens (frob : ℕ → G) (φ : G → ℝ) (x : ℕ) : ℝ :=
  ∑ p ∈ ((Icc 1 x).filter Nat.Prime).filter (fun p : ℕ => ¬ (p : ℤ) ∣ discr L),
    φ (frob p) * (Real.log p / p)

variable {L}

/-- **Unramified primes have trivial inertia**: if `p ∤ disc L`, every prime of `𝓞_L` above `p` has
ramification index `1`, hence trivial inertia group. -/
theorem inertia_eq_bot_of_not_dvd_discr {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr L)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] : P.inertia G = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hunr := (NumberField.not_dvd_discr_iff_isUnramifiedIn L (𝓞 L)
    (Nat.prime_iff_prime_int.mp hp)).mp hd
  have he := Algebra.IsUnramifiedIn.ramificationIdx_eq_one hunr
    (inferInstance : P.LiesOver (span {(p : ℤ)}))
  have hcard := card_inertia_eq_ramificationIdxIn (G := G) (span {(p : ℤ)}) P
  rw [ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P G, he] at hcard
  exact Subgroup.card_eq_one.mp hcard

variable (L G) in
/-- **Frobenius choices exist**: every prime has a prime of `𝓞_L` above it, and every such prime an
arithmetic Frobenius. -/
theorem exists_isFrobeniusChoice : ∃ frob : ℕ → G, IsFrobeniusChoice L frob := by
  have h : ∀ p : ℕ, ∃ σ : G, p.Prime → ¬ (p : ℤ) ∣ discr L → ∃ P : Ideal (𝓞 L),
      P.IsPrime ∧ P.LiesOver (span {(p : ℤ)}) ∧ IsArithFrobAt ℤ σ P := by
    intro p
    by_cases hp : p.Prime
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨⟨P, hP, hPp⟩⟩ := (inferInstance : Nonempty (primesOver (span {(p : ℤ)}) (𝓞 L)))
      have : Finite (𝓞 L ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient (ne_bot_of_liesOver p P)
      obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ G P
      exact ⟨σ, fun _ _ => ⟨P, hP, hPp, hσ⟩⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose frob hfrob using h
  exact ⟨frob, fun p hp hd => hfrob p hp hd⟩

/-- **The permutation character counts degree-one primes**: `π_H(Frob_p) = n_{L^H}(p)` for
`p ∤ disc L`. -/
theorem permChar_frob_eq {frob : ℕ → G} (hfrob : IsFrobeniusChoice L frob) (H : Subgroup G)
    {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr L) :
    permChar H (frob p) = degreeOneCount (invariantField L H) p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, hPp, hσ⟩ := hfrob p hp hd
  have h := card_mul_degreeOneCount_eq (H := H) p P
    (fun Q _ _ => inertia_eq_bot_of_not_dvd_discr hp hd Q) hσ
  have hH : (0 : ℝ) < Nat.card H := by exact_mod_cast Nat.card_pos
  rw [permChar, div_eq_iff hH.ne', ← h]
  push_cast
  ring

/-- The **ramified part** `Σ_{p ≤ x, p ∣ disc L} n_{L^H}(p) log p/p`. -/
def ramifiedMertens (H : Subgroup G) (x : ℕ) : ℝ :=
  ∑ p ∈ ((Icc 1 x).filter Nat.Prime).filter (fun p : ℕ => (p : ℤ) ∣ discr L),
    (degreeOneCount (invariantField L H) p : ℝ) * (Real.log p / p)

theorem degreeOneMertens_eq {frob : ℕ → G} (hfrob : IsFrobeniusChoice L frob) (H : Subgroup G)
    (x : ℕ) :
    degreeOneMertens (invariantField L H) x =
      ramifiedMertens (L := L) H x + frobMertens L frob (permChar H) x := by
  rw [degreeOneMertens, ← sum_filter_add_sum_filter_not _ (fun p : ℕ => (p : ℤ) ∣ discr L),
    ramifiedMertens, frobMertens]
  congr 1
  refine sum_congr rfl fun p hp => ?_
  simp only [mem_filter] at hp
  rw [permChar_frob_eq hfrob H hp.1.2 hp.2]

omit [Fintype G] [IsGaloisGroup G ℚ L] in
theorem ramifiedMertens_nonneg (H : Subgroup G) (x : ℕ) : 0 ≤ ramifiedMertens (L := L) H x :=
  sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _)
    (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))

omit [Fintype G] [IsGaloisGroup G ℚ L] in
/-- **Ramified primes are a bounded error**: they divide `disc L ≠ 0`, so lie below `|disc L|`. -/
theorem ramifiedMertens_le (H : Subgroup G) (x : ℕ) :
    ramifiedMertens (L := L) H x ≤ ramifiedMertens (L := L) H (discr L).natAbs := by
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  simp only [mem_filter, mem_Icc] at hp ⊢
  refine ⟨⟨⟨hp.1.1.1, ?_⟩, hp.1.2⟩, hp.2⟩
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr (discr_ne_zero L)) (Int.natCast_dvd.mp hp.2)

/-- **Mertens' theorem for permutation characters**:
`Σ_{p ≤ x, p ∤ disc L} π_H(Frob_p) log p/p ∼ log x`. -/
theorem tendsto_frobMertens_permChar_div_log {frob : ℕ → G} (hfrob : IsFrobeniusChoice L frob)
    (H : Subgroup G) :
    Tendsto (fun x : ℕ => frobMertens L frob (permChar H) x / Real.log x) atTop (𝓝 1) := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun x : ℕ => ramifiedMertens (L := L) H x / Real.log x) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_
      ((tendsto_const_nhds (x := ramifiedMertens (L := L) H (discr L).natAbs)).div_atTop hlog)
    · filter_upwards [hlog.eventually_ge_atTop 0] with x hx
      exact div_nonneg (ramifiedMertens_nonneg H x) hx
    · filter_upwards [hlog.eventually_ge_atTop 0] with x hx
      exact div_le_div_of_nonneg_right (ramifiedMertens_le H x) hx
  have h := (tendsto_degreeOneMertens_div_log (K := invariantField L H)).sub hR
  rw [sub_zero] at h
  refine h.congr fun x => ?_
  rw [degreeOneMertens_eq hfrob H x]
  ring

end GaloisForLFunctions.ArtinMertens
