/-
The reduction of the integer zero-index to the mod-`n` deck class, and the exact measure of
what that reduction discards.

The deck class of the coarse cocycle around a box is `exp(2πi·(Σ mᵢ)/n)` — the root of unity
read off from the **integer** total order `Σ mᵢ` of the enclosed zeros (`deckClass_multi_zero`).
As a map of that integer index it is the homomorphism `deckRed n : (ℤ,+) → (ℂ,×)`,
`k ↦ exp(2πi·k/n)`, whose kernel is exactly the multiples of `n`.  So the deck class retains only
the residue `index mod n` and discards the quotient `index / n`: two configurations whose total
orders are congruent mod `n` are indistinguishable to it.

At `n = 2` the residue is a single bit — the parity — and the discarded quotient is the pair count.
A configuration invariant under a fixed-point-free involution matching multiplicities (a reflection
pairing of off-line zeros) has even total order, so it lies entirely in the kernel: the parity is
blind to it.  Together with the even order forced at the reflection's fixed point
(`analyticOrderAt_even_of_reflection`), the whole reflection-symmetric part of the index is discarded;
the parity's nonzero signal comes only from the genuinely unpaired, unramified order.
-/
import GaloisForLFunctions.RHTower.DeckMultiZero
import GaloisForLFunctions.RHTower.ReflectionParity

open Complex

namespace RHTower

/-! ### §1 The reduction homomorphism `ℤ → ℂ`, `k ↦ exp(2πi·k/n)` -/

/-- The mod-`n` deck reduction of an integer index: the root of unity the coarse cocycle reads. -/
noncomputable def deckRed (n : ℕ) (k : ℤ) : ℂ := exp (2 * (Real.pi : ℂ) * I * (k : ℂ) / (n : ℂ))

theorem deckRed_ne_zero (n : ℕ) (k : ℤ) : deckRed n k ≠ 0 := Complex.exp_ne_zero _

theorem deckRed_zero (n : ℕ) : deckRed n 0 = 1 := by simp [deckRed]

/-- `deckRed n` is additive-to-multiplicative: it is a homomorphism `(ℤ,+) → (ℂ,×)`. -/
theorem deckRed_add (n : ℕ) (j k : ℤ) : deckRed n (j + k) = deckRed n j * deckRed n k := by
  rw [deckRed, deckRed, deckRed, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem deckRed_neg (n : ℕ) (k : ℤ) : deckRed n (-k) = (deckRed n k)⁻¹ := by
  have h : deckRed n k * deckRed n (-k) = 1 := by
    rw [← deckRed_add, add_neg_cancel, deckRed_zero]
  exact eq_inv_of_mul_eq_one_right h

/-- **The kernel of the reduction.** The deck class is trivial exactly on the multiples of `n`:
`exp(2πi·k/n) = 1 ⟺ n ∣ k`. -/
theorem deckRed_eq_one_iff {n : ℕ} (hn : 0 < n) (k : ℤ) :
    deckRed n k = 1 ↔ (n : ℤ) ∣ k := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h2πI : (2 : ℂ) * (Real.pi : ℂ) * I ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  rw [deckRed, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨mm, hm⟩
    rw [div_eq_iff hn0] at hm
    have h2 : (2 * (Real.pi : ℂ) * I) * (k : ℂ) =
        (2 * (Real.pi : ℂ) * I) * ((n : ℂ) * (mm : ℂ)) := by rw [hm]; ring
    exact ⟨mm, by exact_mod_cast mul_left_cancel₀ h2πI h2⟩
  · rintro ⟨mm, rfl⟩
    exact ⟨mm, by push_cast; field_simp⟩

/-- **The fibers of the reduction.** Two indices have the same deck class exactly when they are
congruent mod `n` — the fibers are the cosets of `nℤ`. -/
theorem deckRed_eq_iff {n : ℕ} (hn : 0 < n) (j k : ℤ) :
    deckRed n j = deckRed n k ↔ j ≡ k [ZMOD n] := by
  have hne : deckRed n k ≠ 0 := deckRed_ne_zero n k
  have hstep : deckRed n (j - k) = deckRed n j * (deckRed n k)⁻¹ := by
    rw [sub_eq_add_neg, deckRed_add, deckRed_neg]
  rw [Int.modEq_iff_dvd, ← neg_sub j k, dvd_neg, ← deckRed_eq_one_iff hn (j - k), hstep,
    mul_inv_eq_one₀ hne]

/-- The deck class factors through `ZMod n`. -/
theorem deckRed_eq_iff_zmod {n : ℕ} (hn : 0 < n) (j k : ℤ) :
    deckRed n j = deckRed n k ↔ (j : ZMod n) = (k : ZMod n) := by
  rw [deckRed_eq_iff hn]
  exact (ZMod.intCast_eq_intCast_iff j k n).symm

/-- **Periodicity: the whole coset `k + nℤ` is invisible.** Shifting the index by any multiple of
`n` leaves the deck class unchanged. -/
theorem deckRed_add_mul (n : ℕ) (k q : ℤ) : deckRed n (k + n * q) = deckRed n k := by
  rw [deckRed_add]
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0; simp [deckRed]
  · rw [(deckRed_eq_one_iff hn (n * q)).mpr ⟨q, rfl⟩, mul_one]

/-! ### §2 The box charge is the reduction of the integer index -/

/-- Casting the total order into the reduction: `exp(2πi·(idx)/n) = deckRed n idx`. -/
theorem exp_natCast_index_eq_deckRed (n idx : ℕ) :
    exp (2 * (Real.pi : ℂ) * I * (idx : ℂ) / (n : ℂ)) = deckRed n (idx : ℤ) := by
  rw [deckRed]; push_cast; ring_nf

/-- **The coarse box charge is the mod-`n` reduction of the integer zero-index.**  With the
`deckClass_multi_zero` geometry, any local `n`-th roots on the two slit-annulus charts have deck
class `deckRed n (Σ mᵢ)` — the reduction homomorphism applied to the total order of the enclosed
zeros.  This exhibits the deck class at `n = 2^k` as the image of the integer index (the full
signed count) under `deckRed n`. -/
theorem box_charge_eq_deckRed {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    {f h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    {n : ℕ} (hn : 0 < n)
    (hρ : ∀ i ∈ s, ‖ρ i - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (Metric.ball a R)) (hh0 : ∀ z ∈ Metric.ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ Metric.ball a R, f z = (∏ i ∈ s, (z - ρ i) ^ m i) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ n = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ n = f z) :
    deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) =
      deckRed n (↑(∑ i ∈ s, m i)) := by
  rw [deckClass_multi_zero s ρ m h0 hrR hn hρ hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂, deckRed]
  congr 1
  push_cast
  ring

/-- **The box charge sees only the residue.** Two enclosed configurations whose total orders are
congruent mod `n` produce the same box charge — the deck class is a function of `index mod n`. -/
theorem box_charge_residue {n : ℕ} (hn : 0 < n) {j k : ℤ} (hjk : j ≡ k [ZMOD n]) :
    deckRed n j = deckRed n k := (deckRed_eq_iff hn j k).mpr hjk

/-! ### §3 The discard: what the reduction loses -/

/-- **Per-box blindness to a pair.** At `n = 2`, adding a pair (any even total order) to the enclosed
configuration leaves the deck class unchanged: the parity is blind to interior pair events. -/
theorem parity_blind_to_pair (k : ℤ) : deckRed 2 (k + 2) = deckRed 2 k := by
  have := deckRed_add_mul 2 k 1
  simpa using this

/-- The full even coset is blind: `deckRed 2 (k + 2q) = deckRed 2 k` for every pair count `q`. -/
theorem parity_blind_to_pairs (k q : ℤ) : deckRed 2 (k + 2 * q) = deckRed 2 k :=
  deckRed_add_mul 2 k q

/-- The kernel at `n = 2` is the even integers: `deckRed 2 k = 1 ⟺ Even k`. -/
theorem deckRed_two_eq_one_iff (k : ℤ) : deckRed 2 k = 1 ↔ Even k := by
  rw [deckRed_eq_one_iff (by norm_num : (0:ℕ) < 2), show ((2:ℕ):ℤ) = 2 from by norm_num]
  exact even_iff_two_dvd.symm

/-- **Parity is exactly the mod-2 bit.** At `n = 2` the deck class of the index equals that of
another index exactly when the two have the same parity — the reduction retains a single bit and its
fibers are the cosets of `2ℤ`. -/
theorem deckRed_two_eq_iff_even_sub (j k : ℤ) :
    deckRed 2 j = deckRed 2 k ↔ Even (j - k) := by
  have hne : deckRed 2 k ≠ 0 := deckRed_ne_zero 2 k
  have hstep : deckRed 2 (j - k) = deckRed 2 j * (deckRed 2 k)⁻¹ := by
    rw [sub_eq_add_neg, deckRed_add, deckRed_neg]
  rw [← deckRed_two_eq_one_iff (j - k), hstep, mul_inv_eq_one₀ hne]

/-! ### §4 A fixed-point-free involution forces even index -/

/-- **A reflection pairing has even total order.** If a finite index set carries a fixed-point-free
involution under which the multiplicity is invariant, the total order `Σ mᵢ` is even: the zeros pair
off, each pair contributing `2 mᵢ`. -/
theorem even_sum_of_fpf_involution {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (σ : ι → ι) (m : ι → ℕ)
    (hσs : ∀ i ∈ s, σ i ∈ s) (hσσ : ∀ i ∈ s, σ (σ i) = i)
    (hfix : ∀ i ∈ s, σ i ≠ i) (hm : ∀ i ∈ s, m (σ i) = m i) :
    Even (∑ i ∈ s, m i) := by
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · simp
    · have hσi : σ i ∈ s := hσs i hi
      have hne : σ i ≠ i := hfix i hi
      set s' := (s.erase i).erase (σ i) with hs'_def
      have hσimem : σ i ∈ s.erase i := Finset.mem_erase.mpr ⟨hne, hσi⟩
      have hsub : s' ⊂ s :=
        Finset.ssubset_of_ssubset_of_subset (Finset.erase_ssubset hσimem)
          (Finset.erase_subset i s)
      have hmem' : ∀ j ∈ s', σ j ∈ s' := by
        intro j hj
        rw [hs'_def, Finset.mem_erase, Finset.mem_erase] at hj
        obtain ⟨hjσi, hji, hjs⟩ := hj
        rw [hs'_def, Finset.mem_erase, Finset.mem_erase]
        refine ⟨?_, ?_, hσs j hjs⟩
        · intro heq
          apply hji
          have hh := hσσ j hjs
          rw [heq, hσσ i hi] at hh
          exact hh.symm
        · intro heq
          apply hjσi
          have hh := hσσ j hjs
          rw [heq] at hh
          exact hh.symm
      have hσσ' : ∀ j ∈ s', σ (σ j) = j := fun j hj => hσσ j (by
        rw [hs'_def, Finset.mem_erase, Finset.mem_erase] at hj; exact hj.2.2)
      have hfix' : ∀ j ∈ s', σ j ≠ j := fun j hj => hfix j (by
        rw [hs'_def, Finset.mem_erase, Finset.mem_erase] at hj; exact hj.2.2)
      have hm' : ∀ j ∈ s', m (σ j) = m j := fun j hj => hm j (by
        rw [hs'_def, Finset.mem_erase, Finset.mem_erase] at hj; exact hj.2.2)
      have hrec := ih s' hsub hmem' hσσ' hfix' hm'
      have hsplit : ∑ j ∈ s, m j = (∑ j ∈ s', m j) + m i + m (σ i) := by
        have e1 : (∑ j ∈ s.erase i, m j) + m i = ∑ j ∈ s, m j := Finset.sum_erase_add s m hi
        have e2 : (∑ j ∈ (s.erase i).erase (σ i), m j) + m (σ i) = ∑ j ∈ s.erase i, m j :=
          Finset.sum_erase_add (s.erase i) m hσimem
        rw [hs'_def, ← e1, ← e2]; ring
      rw [hsplit, hm i hi]
      have hxx : (∑ j ∈ s', m j) + m i + m i = (∑ j ∈ s', m j) + 2 * m i := by ring
      rw [hxx]
      exact hrec.add (even_two_mul _)

/-- **A reflection-paired configuration is entirely in the discard.** At `n = 2`, a fixed-point-free
involution with matching multiplicities makes the box charge trivial: the parity is blind to
the reflection-paired zeros. -/
theorem reflection_paired_deckRed_two_eq_one {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (σ : ι → ι) (m : ι → ℕ)
    (hσs : ∀ i ∈ s, σ i ∈ s) (hσσ : ∀ i ∈ s, σ (σ i) = i)
    (hfix : ∀ i ∈ s, σ i ≠ i) (hm : ∀ i ∈ s, m (σ i) = m i) :
    deckRed 2 (↑(∑ i ∈ s, m i)) = 1 := by
  rw [deckRed_two_eq_one_iff]
  exact_mod_cast even_sum_of_fpf_involution s σ m hσs hσσ hfix hm

/-- **The ramified fixed point is in the discard too.** The even order forced at the reflection's
fixed point (`analyticOrderAt_even_of_reflection`) makes its deck class trivial at `n = 2`: the
ramification contributes nothing to the parity either. -/
theorem reflection_fixed_deckRed_two_eq_one {g : ℂ → ℂ} {c : ℂ}
    (hg : AnalyticOnNhd ℂ g Set.univ) (hsym : ∀ s, g (2 * c - s) = g s)
    (hne : analyticOrderAt g c ≠ ⊤) :
    deckRed 2 (↑(analyticOrderAt g c).toNat) = 1 := by
  rw [deckRed_two_eq_one_iff]
  exact_mod_cast analyticOrderAt_even_of_reflection hg hsym hne

/-! ### §5 The measure of the discard -/

/-- **The deck class is the reduction of the residue.**  It depends on the integer index only
through `index mod n`: `deckRed n k = deckRed n (k % n)`.  This is the exact retained datum. -/
theorem deckRed_emod {n : ℕ} (hn : 0 < n) (k : ℤ) : deckRed n k = deckRed n (k % n) := by
  refine box_charge_residue hn ?_
  rw [Int.modEq_iff_dvd]
  exact ⟨-(k / n), by rw [Int.emod_def]; ring⟩

/-- **The discard is a full copy of `ℤ`.**  For each deck class value there is an injective
`ℤ`-family of indices realizing it — the pair/cycle count `q` ranging over all of `ℤ` while the
deck class stays fixed.  So the reduction retains the finite residue and discards a free `ℤ`. -/
theorem parity_discards_full_line {n : ℕ} (hn : 0 < n) (k : ℤ) :
    Function.Injective (fun q : ℤ => k + n * q) ∧
      (∀ q : ℤ, deckRed n (k + n * q) = deckRed n k) := by
  have hn0 : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  refine ⟨fun q q' h => ?_, fun q => deckRed_add_mul n k q⟩
  simp only at h
  exact mul_left_cancel₀ hn0 (add_left_cancel h)


/-- **The signature-to-parity reduction, sharp form.** The integer index determines the deck class,
but the deck class determines the index only modulo `n`: the reduction `deckRed n` has fibers exactly
the cosets `k + nℤ`.  Concretely, for every quotient `q` the index `k + n·q` has the same deck class
as `k`, so the reduction retains the residue `k mod n` and discards the entire quotient `q ∈ ℤ`.  At
`n = 2` the retained datum is a single bit — the parity — and the discarded datum is the pair count. -/
theorem signature_parity_reduction {n : ℕ} (hn : 0 < n) :
    (∀ k q : ℤ, deckRed n (k + n * q) = deckRed n k) ∧
    (∀ j k : ℤ, deckRed n j = deckRed n k ↔ (j : ZMod n) = (k : ZMod n)) :=
  ⟨fun k q => deckRed_add_mul n k q, fun j k => deckRed_eq_iff_zmod hn j k⟩

/-- **The parity retains one bit and discards the pair count.**  At `n = 2` the deck class is
the reduction of `k % 2 ∈ {0, 1}` — a single retained bit — while the pair count `k / 2`, ranging
over all of `ℤ`, is invisible: `k = 2·(k / 2) + (k % 2)` splits the integer index into the discarded
quotient and the retained bit. -/
theorem parity_one_bit_retained (k : ℤ) :
    deckRed 2 k = deckRed 2 (k % 2) ∧ (k % 2 = 0 ∨ k % 2 = 1) ∧
      k = 2 * (k / 2) + k % 2 :=
  ⟨deckRed_emod (by norm_num) k, Int.emod_two_eq_zero_or_one k, by omega⟩

end RHTower
