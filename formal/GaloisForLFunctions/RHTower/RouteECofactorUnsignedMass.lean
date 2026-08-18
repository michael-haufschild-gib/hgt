import GaloisForLFunctions.RHTower.RouteECofactorParityBalance
import GaloisForLFunctions.RHTower.Sieve.CoprimeSquarefreeHarmonic

/-!
# The unsigned squarefree mass of a band-avoiding parity class

`RouteECofactorParityBalance` reduces each Möbius parity class of band-avoiding cofactors to the
odd band-avoiding squarefree source set, at the cost of one factor from the pairing `s ↔ 2s`.  This
file supplies the missing *unsigned* estimate for that source set — the card's `(7)` and `(9)` — by
identifying it with the squarefree integers coprime to `Q = 2 ∏_{p ∈ B} p` and applying
`Sieve/CoprimeSquarefreeHarmonic`.

The only hypothesis is that the excluded band carries little Mertens mass, `∑_{p ∈ B} 1/p ≤ 1/8`,
which the card's polylogarithmic band satisfies with room to spare: its mass is
`log(a₁/a₀) + o(1)` with `a₁/a₀ ≤ 1.1/(1.1 − 10⁻⁴)`.

The parity-balance step is generalised here to an arbitrary antitone weight, so that it serves the
square-root weight of `(7)` as well as the harmonic weight of `(9)`.
-/

namespace RHTower

namespace CofactorParity

open Finset

noncomputable section

variable {Band : ℕ → Prop} [DecidablePred Band]

/-- **Parity balance for an arbitrary antitone weight.**  Each parity class carries at least the
weight of the doubled odd band-avoiding squarefree source set. -/
theorem sum_oddBase_two_mul_le_sum_parityClass (hband : ¬ Band 2) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (T : ℕ) {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n)
    (hanti : ∀ {m n : ℕ}, 1 ≤ m → m ≤ n → w n ≤ w m) :
    ∑ s ∈ oddBase Band T, w (2 * s) ≤ ∑ t ∈ parityClass Band σ T, w t := by
  classical
  have hsub : (oddBase Band T).image (pairMap σ) ⊆ parityClass Band σ T := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨s, hs, rfl⟩ := hq
    exact pairMap_mem hband hσ hs
  have himg : ∑ q ∈ (oddBase Band T).image (pairMap σ), w q
      = ∑ s ∈ oddBase Band T, w (pairMap σ s) :=
    Finset.sum_image (f := fun q : ℕ => w q) pairMap_injOn
  calc ∑ s ∈ oddBase Band T, w (2 * s)
      ≤ ∑ s ∈ oddBase Band T, w (pairMap σ s) :=
        Finset.sum_le_sum fun s hs =>
          hanti (one_le_pairMap ((mem_oddBase_iff).mp hs).1.1) (pairMap_le (σ := σ) (s := s))
    _ = ∑ q ∈ (oddBase Band T).image (pairMap σ), w q := himg.symm
    _ ≤ ∑ t ∈ parityClass Band σ T, w t :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => hw0 i

end

end CofactorParity

/-! ## The band as a coprimality condition -/

open Finset

noncomputable section

/-- The modulus carrying the prime `2` and the whole excluded band. -/
def bandModulus (B : Finset ℕ) : ℕ := 2 * ∏ p ∈ B, p

theorem bandModulus_ne_zero {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) : bandModulus B ≠ 0 := by
  have hprod : 0 < ∏ p ∈ B, p := Finset.prod_pos fun p hp => (hB p hp).pos
  rw [bandModulus]
  omega

theorem two_dvd_bandModulus (B : Finset ℕ) : 2 ∣ bandModulus B := ⟨∏ p ∈ B, p, rfl⟩

/-- A prime dividing the modulus is either `2` or a band prime. -/
theorem primeFactors_bandModulus_subset {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) :
    (bandModulus B).primeFactors ⊆ insert 2 B := by
  intro r hr
  rw [Nat.mem_primeFactors] at hr
  obtain ⟨hrp, hrQ, _⟩ := hr
  rw [bandModulus] at hrQ
  rcases (Nat.Prime.dvd_mul hrp).1 hrQ with h2 | hprod
  · have : r = 2 := (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).1 h2
    exact Finset.mem_insert.2 (Or.inl this)
  · obtain ⟨q, hq, hrq⟩ := (Prime.dvd_finsetProd_iff hrp.prime _).1 hprod
    have : r = q := (Nat.prime_dvd_prime_iff_eq hrp (hB q hq)).1 hrq
    exact Finset.mem_insert.2 (Or.inr (this ▸ hq))

/-- **The Mertens mass of the modulus.** -/
theorem sum_inv_primeFactors_bandModulus_le {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime)
    (hBsum : ∑ p ∈ B, 1 / (p : ℝ) ≤ 1 / 8) :
    ∑ p ∈ (bandModulus B).primeFactors, 1 / (p : ℝ) ≤ 5 / 8 := by
  classical
  have hnn : ∀ p ∈ insert 2 B, p ∉ (bandModulus B).primeFactors → (0 : ℝ) ≤ 1 / (p : ℝ) :=
    fun p _ _ => by positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (primeFactors_bandModulus_subset hB) hnn) ?_
  by_cases h2 : (2 : ℕ) ∈ B
  · rw [Finset.insert_eq_self.2 h2]
    linarith [hBsum]
  · rw [Finset.sum_insert h2, show (1 : ℝ) / ((2 : ℕ) : ℝ) = 1 / 2 from by norm_num]
    linarith [hBsum]

/-- **The band condition is coprimality to the modulus.** -/
theorem coprime_bandModulus_iff {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {s : ℕ} (hs : s ≠ 0) :
    Nat.Coprime s (bandModulus B) ↔ (¬ (2 ∣ s) ∧ ∀ p ∈ s.primeFactors, p ∉ B) := by
  classical
  constructor
  · intro hcop
    refine ⟨?_, ?_⟩
    · intro h2
      have hdvd : (2 : ℕ) ∣ Nat.gcd s (bandModulus B) :=
        Nat.dvd_gcd h2 (two_dvd_bandModulus B)
      have h1 : (2 : ℕ) ∣ 1 := hcop ▸ hdvd
      omega
    · intro p hp hpB
      have hps : p ∣ s := Nat.dvd_of_mem_primeFactors hp
      have hpQ : p ∣ bandModulus B := by
        rw [bandModulus]
        exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hpB) 2
      have hdvd : p ∣ Nat.gcd s (bandModulus B) := Nat.dvd_gcd hps hpQ
      have h1 : p ∣ 1 := hcop ▸ hdvd
      have hp1 : p = 1 := Nat.eq_one_of_dvd_one h1
      exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' hp1
  · rintro ⟨h2, hband⟩
    by_contra hcop
    obtain ⟨r, hr, hrg⟩ := Nat.exists_prime_and_dvd hcop
    have hrs : r ∣ s := hrg.trans (Nat.gcd_dvd_left _ _)
    have hrQ : r ∣ bandModulus B := hrg.trans (Nat.gcd_dvd_right _ _)
    rw [bandModulus] at hrQ
    rcases (Nat.Prime.dvd_mul hr).1 hrQ with hr2 | hprod
    · have : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hr2
      exact h2 (this ▸ hrs)
    · obtain ⟨q, hq, hrq⟩ := (Prime.dvd_finsetProd_iff hr.prime _).1 hprod
      have hrq' : r = q := (Nat.prime_dvd_prime_iff_eq hr (hB q hq)).1 hrq
      exact hband r (Nat.mem_primeFactors.2 ⟨hr, hrs, hs⟩) (hrq' ▸ hq)

/-- **The source set of the pairing is the coprime squarefree set.** -/
theorem oddBase_eq_coprime_squarefree {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (T : ℕ) :
    CofactorParity.oddBase (fun p => p ∈ B) T
      = (Finset.Icc 1 (T / 2)).filter
          (fun s => Nat.Coprime s (bandModulus B) ∧ Squarefree s) := by
  classical
  ext s
  rw [CofactorParity.mem_oddBase_iff, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hsq, hodd, hband⟩
    exact ⟨⟨h1, h2⟩, (coprime_bandModulus_iff hB (by omega)).2 ⟨hodd, hband⟩, hsq⟩
  · rintro ⟨⟨h1, h2⟩, hcop, hsq⟩
    obtain ⟨hodd, hband⟩ := (coprime_bandModulus_iff hB (by omega)).1 hcop
    exact ⟨⟨h1, h2⟩, hsq, hodd, hband⟩

/-! ## The card's `(7)` and `(9)` -/

/-- **`(9)`: the harmonic mass of a band-avoiding parity class.**  Every Möbius parity class of
band-avoiding cofactors below `T` carries harmonic mass `≫ log T`, unconditionally. -/
theorem sum_inv_parityClass_ge {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime)
    (hBsum : ∑ p ∈ B, 1 / (p : ℝ) ≤ 1 / 8) (h2B : 2 ∉ B) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {T : ℕ} (hT : 1 ≤ T / 2) :
    (1 / 16 : ℝ) * Real.log ((T / 2 : ℕ) : ℝ) - 7 / 16
      ≤ ∑ t ∈ CofactorParity.parityClass (fun p => p ∈ B) σ T, 1 / (t : ℝ) := by
  classical
  have hsource : (1 / 8 : ℝ) * Real.log ((T / 2 : ℕ) : ℝ) - 7 / 8
      ≤ ∑ s ∈ CofactorParity.oddBase (fun p => p ∈ B) T, 1 / (s : ℝ) := by
    rw [oddBase_eq_coprime_squarefree hB T]
    exact Sieve.sum_inv_coprime_squarefree_ge (bandModulus_ne_zero hB)
      (two_dvd_bandModulus B) hT (sum_inv_primeFactors_bandModulus_le hB hBsum)
  have hbalance := CofactorParity.sum_oddBase_two_mul_le_sum_parityClass
    (Band := fun p => p ∈ B) (by simpa using h2B) hσ T
    (w := fun n : ℕ => 1 / (n : ℝ)) (fun n => by positivity)
    (fun {m n} hm hmn => by
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      exact one_div_le_one_div_of_le hm0 (by exact_mod_cast hmn))
  have hhalf : ∀ s : ℕ, (1 / ((2 * s : ℕ) : ℝ)) = (1 / 2) * (1 / (s : ℝ)) := by
    intro s
    rw [Nat.cast_mul]
    push_cast
    rw [one_div, one_div, mul_inv]
    norm_num
  rw [Finset.sum_congr rfl (fun s _ => hhalf s), ← Finset.mul_sum] at hbalance
  linarith [hsource, hbalance]

/-- **`(7)`: the square-root mass of a band-avoiding parity class.**  Every Möbius parity class of
band-avoiding cofactors below `T` carries square-root mass `≫ √T`, unconditionally. -/
theorem sum_inv_sqrt_parityClass_ge {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime)
    (hBsum : ∑ p ∈ B, 1 / (p : ℝ) ≤ 1 / 8) (h2B : 2 ∉ B) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (T : ℕ) :
    (1 / 8 : ℝ) * Real.sqrt ((T / 2 : ℕ) : ℝ) - 1
      ≤ ∑ t ∈ CofactorParity.parityClass (fun p => p ∈ B) σ T, 1 / Real.sqrt (t : ℝ) := by
  classical
  have hsource : (1 / 4 : ℝ) * Real.sqrt ((T / 2 : ℕ) : ℝ) - 2
      ≤ ∑ s ∈ CofactorParity.oddBase (fun p => p ∈ B) T, 1 / Real.sqrt (s : ℝ) := by
    rw [oddBase_eq_coprime_squarefree hB T]
    exact Sieve.sum_inv_sqrt_coprime_squarefree_ge (bandModulus_ne_zero hB)
      (two_dvd_bandModulus B) (sum_inv_primeFactors_bandModulus_le hB hBsum)
  have hbalance := CofactorParity.sum_oddBase_two_mul_le_sum_parityClass
    (Band := fun p => p ∈ B) (by simpa using h2B) hσ T
    (w := fun n : ℕ => 1 / Real.sqrt (n : ℝ)) (fun n => by positivity)
    (fun {m n} hm hmn => by
      have hm0 : (0 : ℝ) < Real.sqrt (m : ℝ) := by
        refine Real.sqrt_pos.2 ?_
        exact_mod_cast hm
      exact one_div_le_one_div_of_le hm0 (Real.sqrt_le_sqrt (by exact_mod_cast hmn)))
  have hhalf : ∀ s : ℕ,
      (1 / Real.sqrt ((2 * s : ℕ) : ℝ)) ≥ (1 / 2) * (1 / Real.sqrt (s : ℝ)) := by
    intro s
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp
    have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
    have hsq : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hs0
    have hcast : (((2 * s : ℕ)) : ℝ) = 2 * (s : ℝ) := by push_cast; ring
    rw [hcast, Real.sqrt_mul (by norm_num)]
    have h2 : Real.sqrt 2 ≤ 2 := by
      have : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    rw [ge_iff_le]
    have h2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hle : Real.sqrt 2 * Real.sqrt (s : ℝ) ≤ 2 * Real.sqrt (s : ℝ) :=
      mul_le_mul_of_nonneg_right h2 hsq.le
    have h2s : (0 : ℝ) < Real.sqrt 2 * Real.sqrt (s : ℝ) := by positivity
    have hstep : 1 / (2 * Real.sqrt (s : ℝ)) ≤ 1 / (Real.sqrt 2 * Real.sqrt (s : ℝ)) :=
      one_div_le_one_div_of_le h2s hle
    have heq : (1 / 2 : ℝ) * (1 / Real.sqrt (s : ℝ)) = 1 / (2 * Real.sqrt (s : ℝ)) := by
      field_simp
    linarith [hstep, heq.le, heq.ge]
  have hstep : (1 / 2 : ℝ) * ∑ s ∈ CofactorParity.oddBase (fun p => p ∈ B) T,
        1 / Real.sqrt (s : ℝ)
      ≤ ∑ s ∈ CofactorParity.oddBase (fun p => p ∈ B) T, 1 / Real.sqrt ((2 * s : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun s _ => hhalf s
  linarith [hsource, hbalance, hstep]

end

end RHTower
