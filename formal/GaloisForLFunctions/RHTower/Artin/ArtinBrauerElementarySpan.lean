import GaloisForLFunctions.RHTower.Artin.ArtinRegularClassSum
import GaloisForLFunctions.RHTower.Artin.ArtinInducedSpanDescent

/-!
# Brauer's theorem: the characters induced from elementary subgroups span

For a finite group `G`, every virtual character is an integer combination of characters induced
from Brauer-elementary subgroups (`inducedSpan_brauerElementaryFamily`).

Let `V` be the span, over the algebraic integers `𝓞`, of the characters induced from the
elementary subgroups; it is an ideal of the `𝓞`-span of the characters and contains every class
function with values in `|G|·𝓞`.

* For a prime `p` write `|G| = p^n l`. The function `Ψ = regularClassSum p` lies in `V` and has
  integer values prime to `p`, so `Ψ^N ≡ 1 (mod p^n)` for `N = φ(p^n)` by Euler's theorem. Then
  `l (Ψ^N − 1)` has values in `|G|·ℤ` and lies in `V`, and `l Ψ^N` lies in `V` because `V` is an
  ideal. Hence the constant `l` lies in `V` (`ordCompl_mem_inducedSpanInt`).
* The constants in `V` form a subgroup of `ℤ` containing `|G|` and every `l`; by Bézout it
  contains `1` (`one_mem_inducedSpanInt_brauerElementary`).
* A virtual character in `V` is an integer combination of the induced characters, and the
  integer span is an ideal of the ring of virtual characters.
-/

open scoped Classical BigOperators

noncomputable section

universe u

namespace GaloisForLFunctions

variable {G : Type u} [Group G] [Fintype G]

/-- The constant `|G|` is a combination of characters induced from cyclic subgroups. -/
theorem card_mem_inducedSpanInt :
    (fun _ : G => (Nat.card G : ℂ)) ∈ inducedSpanInt (brauerElementaryFamily G) :=
  mem_inducedSpanInt_of_card_mul zpowers_mem_brauerElementaryFamily (fun _ _ => rfl)
    fun _ => ⟨1, isIntegral_one, (mul_one _).symm⟩

/-- **The prime-to-`p` part of `|G|` is an `𝓞`-combination of characters induced from
elementary subgroups.** -/
theorem ordCompl_mem_inducedSpanInt {p : ℕ} (hp : p.Prime) :
    (fun _ : G => ((Nat.card G / p ^ (Nat.card G).factorization p : ℕ) : ℂ)) ∈
      inducedSpanInt (brauerElementaryFamily G) := by
  obtain ⟨n, l, hnl, hl⟩ : ∃ n l : ℕ, p ^ n * l = Nat.card G ∧
      l = Nat.card G / p ^ (Nat.card G).factorization p :=
    ⟨_, _, Nat.ordProj_mul_ordCompl_eq_self _ p, rfl⟩
  rw [← hl]
  have hΨ := regularClassSum_mem_inducedSpanInt hp (G := G)
  have hΨv := inducedSpanInt_le_virtualIntGroup _ hΨ
  choose a ha hΨa using exists_nat_not_dvd_regularClassSum hp (G := G)
  obtain ⟨N, hN⟩ : ∃ N, N = Nat.totient (p ^ n) := ⟨_, rfl⟩
  have hNpos : 0 < N := by
    rw [hN]
    exact Nat.totient_pos.mpr (pow_pos hp.pos n)
  -- Euler: the values of `Ψ^N` are `≡ 1 (mod p^n)`
  have heuler : ∀ g : G, ∃ t : ℕ, a g ^ N = 1 + p ^ n * t := by
    intro g
    have hcop : (a g).Coprime (p ^ n) :=
      Nat.Coprime.pow_right n (hp.coprime_iff_not_dvd.mpr (ha g)).symm
    have h := Nat.ModEq.pow_totient hcop
    rw [← hN] at h
    have h1 : 1 ≤ a g ^ N := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h0 => ha g (by
      rw [h0]
      exact dvd_zero p))
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' h1).mp h.symm
    exact ⟨t, by omega⟩
  choose t ht using heuler
  -- `l (Ψ^N − 1)` has values in `|G|·ℤ`
  have hf : (fun g : G => (l : ℂ) * (regularClassSum p g ^ N - 1)) ∈
      inducedSpanInt (brauerElementaryFamily G) := by
    refine mem_inducedSpanInt_of_card_mul zpowers_mem_brauerElementaryFamily (fun x g => ?_)
      fun g => ⟨(t g : ℂ), isIntegral_natCast_complex _, ?_⟩
    · show (l : ℂ) * (regularClassSum p (x * g * x⁻¹) ^ N - 1) = _
      rw [virtualIntGroup_conj hΨv x g]
    · show (l : ℂ) * (regularClassSum p g ^ N - 1) = _
      rw [hΨa g, ← Nat.cast_pow, ht g, ← hnl]
      push_cast
      ring
  -- `l Ψ^N` lies in the ideal
  have hmul := mul_mem_inducedSpanInt hΨ (smul_mem_virtualIntGroup (isIntegral_natCast_complex l)
    (pow_mem_virtualIntGroup hΨv (N - 1)))
  have hconst : (fun _ : G => (l : ℂ)) =
      (regularClassSum p * fun g => (l : ℂ) * (regularClassSum p ^ (N - 1)) g) -
        fun g => (l : ℂ) * (regularClassSum p g ^ N - 1) := by
    funext g
    have hpow : regularClassSum p g ^ N = regularClassSum p g ^ (N - 1) * regularClassSum p g := by
      rw [← pow_succ, Nat.sub_add_cancel hNpos]
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    rw [hpow]
    ring
  rw [hconst]
  exact sub_mem hmul hf

/-- **The constant `1` is an `𝓞`-combination of characters induced from elementary
subgroups.** A constant `m > 1` in the span is replaced by `gcd(m, l)`, with `l` the part of
`|G|` prime to a prime divisor of `m`. -/
theorem one_mem_inducedSpanInt_brauerElementary :
    (1 : G → ℂ) ∈ inducedSpanInt (brauerElementaryFamily G) := by
  have key : ∀ m : ℕ, 0 < m →
      (fun _ : G => (m : ℂ)) ∈ inducedSpanInt (brauerElementaryFamily G) →
        (1 : G → ℂ) ∈ inducedSpanInt (brauerElementaryFamily G) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm hmem
      by_cases h1 : m = 1
      · have e : (fun _ : G => (m : ℂ)) = 1 := by
          rw [h1, Nat.cast_one]
          rfl
        rwa [e] at hmem
      · obtain ⟨p, hp, hpm⟩ : ∃ p, p.Prime ∧ p ∣ m := ⟨_, Nat.minFac_prime h1, Nat.minFac_dvd m⟩
        obtain ⟨l, hl⟩ : ∃ l, l = Nat.card G / p ^ (Nat.card G).factorization p := ⟨_, rfl⟩
        have hlmem := ordCompl_mem_inducedSpanInt hp (G := G)
        rw [← hl] at hlmem
        have hpl : ¬ p ∣ l := by
          rw [hl]
          exact Nat.not_dvd_ordCompl hp Nat.card_pos.ne'
        -- `gcd(m, l) < m` because `p` divides `m` and not `l`
        have hglt : Nat.gcd m l < m := by
          refine lt_of_le_of_ne (Nat.le_of_dvd hm (Nat.gcd_dvd_left m l)) fun hg => hpl ?_
          have hml := Nat.gcd_dvd_right m l
          rw [hg] at hml
          exact hpm.trans hml
        refine ih _ hglt (Nat.gcd_pos_of_pos_left l hm) ?_
        -- Bézout
        have hbez : ((Nat.gcd m l : ℕ) : ℂ) =
            (m : ℂ) * (Nat.gcdA m l : ℂ) + (l : ℂ) * (Nat.gcdB m l : ℂ) := by
          have h := congrArg (Int.cast : ℤ → ℂ) (Nat.gcd_eq_gcd_ab m l)
          push_cast at h
          exact h
        have e : (fun _ : G => ((Nat.gcd m l : ℕ) : ℂ)) =
            Nat.gcdA m l • (fun _ : G => (m : ℂ)) + Nat.gcdB m l • fun _ : G => (l : ℂ) := by
          funext g
          show ((Nat.gcd m l : ℕ) : ℂ) = Nat.gcdA m l • (m : ℂ) + Nat.gcdB m l • (l : ℂ)
          rw [zsmul_eq_mul, zsmul_eq_mul, hbez]
          ring
        rw [e]
        exact add_mem (zsmul_mem hmem _) (zsmul_mem hlmem _)
  exact key (Nat.card G) Nat.card_pos card_mem_inducedSpanInt

/-- **Brauer's theorem on elementary subgroups.** Every virtual character of a finite group is
an integer combination of characters induced from Brauer-elementary subgroups. -/
theorem inducedSpan_brauerElementaryFamily :
    inducedSpan (brauerElementaryFamily G) = virtualCharacterGroup G :=
  inducedSpan_eq_of_one_mem (mem_inducedSpan_of_mem_inducedSpanInt
    (AddSubgroup.subset_closure one_mem_fdCharacterSet) one_mem_inducedSpanInt_brauerElementary)

end GaloisForLFunctions
