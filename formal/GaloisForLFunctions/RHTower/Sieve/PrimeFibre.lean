import GaloisForLFunctions.RHTower.Sieve.IndicatorExpSum

/-!
# The prime fibre of the Farey set

At a prime denominator the two halves of Montgomery's sieve index the same set of fractions:
the lower bound of `MontgomerySieve.lean` runs over the nonzero residues modulo `p`, and the Farey
set of order `Q` contains, above the denominator `p ≤ Q`, exactly the fractions `a/p` with
`1 ≤ a < p` — because a numerator coprime to a prime is simply a numerator not divisible by it.

Identifying the two turns the lower bound into a statement about the very sum the large sieve
bounds, which is the last structural step before the sieve inequality itself.
-/

namespace RHTower.Sieve

open Finset

/-- Erasing the zero frequency, over `Fin p` or over `range p`, gives the same sum. -/
theorem sum_erase_fin_eq_range {p : ℕ} (hp : 0 < p) (F : ℕ → ℝ) :
    ∑ j ∈ (Finset.univ : Finset (Fin p)).erase ⟨0, hp⟩, F (j : ℕ)
      = ∑ a ∈ (Finset.range p).erase 0, F a := by
  classical
  have h1 := Finset.add_sum_erase (Finset.univ : Finset (Fin p)) (fun j : Fin p => F (j : ℕ))
    (Finset.mem_univ (⟨0, hp⟩ : Fin p))
  have h2 := Finset.add_sum_erase (Finset.range p) F (Finset.mem_range.mpr hp)
  have h3 : ∑ j : Fin p, F (j : ℕ) = ∑ a ∈ Finset.range p, F a := Fin.sum_univ_eq_sum_range F p
  have hval : ((⟨0, hp⟩ : Fin p) : ℕ) = 0 := rfl
  rw [hval] at h1
  linarith [h1, h2, h3]

/-- **The fibre of the Farey set above a prime denominator.** -/
theorem fareySet_fibre_prime {p : ℕ} (hp : p.Prime) {Q : ℕ} (hpQ : p ≤ Q) :
    (fareySet Q).filter (fun x => x.2 = p)
      = ((Finset.range p).erase 0).image (fun a => (a, p)) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_erase, Finset.mem_range,
    mem_fareySet]
  constructor
  · rintro ⟨⟨⟨hx1, _⟩, ⟨_, _⟩, hle, hcop⟩, hx2⟩
    refine ⟨x.1, ⟨?_, ?_⟩, ?_⟩
    · omega
    · rcases lt_or_eq_of_le (hx2 ▸ hle) with hlt | heq
      · exact hlt
      · exfalso
        rw [heq, hx2] at hcop
        have hone : p = 1 := by
          have hg := hcop
          rwa [Nat.Coprime, Nat.gcd_self] at hg
        exact hp.one_lt.ne' hone
    · rw [← hx2]
  · rintro ⟨a, ⟨ha0, hap⟩, rfl⟩
    have hnd : ¬ p ∣ a := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero ha0) hap
    have hcop : Nat.Coprime a p := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd |>.symm
    refine ⟨⟨⟨?_, ?_⟩, ⟨hp.pos, hpQ⟩, ?_, hcop⟩, rfl⟩
    · omega
    · omega
    · omega

/-- **The lower-bound index set is the prime fibre.** -/
theorem sum_fareySet_fibre_eq {p : ℕ} (hp : p.Prime) {Q : ℕ} (hpQ : p ≤ Q) (A : Finset ℕ) :
    ∑ x ∈ (fareySet Q).filter (fun x => x.2 = p),
        ‖∑ n ∈ A, circleFreq ((n : ℝ) * ((x.1 : ℝ) / (x.2 : ℝ)))‖ ^ 2
      = ∑ j ∈ (Finset.univ : Finset (Fin p)).erase ⟨0, hp.pos⟩,
          ‖∑ n ∈ A, circleFreq (((n * (j : ℕ) : ℕ) : ℝ) / (p : ℝ))‖ ^ 2 := by
  classical
  rw [sum_erase_fin_eq_range hp.pos
    (fun a => ‖∑ n ∈ A, circleFreq (((n * a : ℕ) : ℝ) / (p : ℝ))‖ ^ 2)]
  rw [fareySet_fibre_prime hp hpQ]
  have hinj : ∀ a ∈ (Finset.range p).erase 0, ∀ a' ∈ (Finset.range p).erase 0,
      ((a, p) : ℕ × ℕ) = (a', p) → a = a' := fun a _ a' _ heq => congrArg Prod.fst heq
  rw [Finset.sum_image hinj]
  have harg : ∀ n a : ℕ, (n : ℝ) * ((a : ℝ) / (p : ℝ)) = ((n * a : ℕ) : ℝ) / (p : ℝ) := by
    intro n a
    push_cast
    ring
  refine Finset.sum_congr rfl fun a _ => ?_
  refine congrArg (fun z : ℂ => ‖z‖ ^ 2) ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [harg]

end RHTower.Sieve
