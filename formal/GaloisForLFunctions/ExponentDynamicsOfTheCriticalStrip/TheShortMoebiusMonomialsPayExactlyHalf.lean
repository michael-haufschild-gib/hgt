import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheMoebiusSignCostsHalfAUnitAtSomePlace

/-!
# The short Möbius monomials pay exactly half

A Möbius-signed Gauss monomial of `r` nontrivial characters of `𝔽_p` has half-integral Stickelberger
defect (`isMoebiusSignedTuple_iff_defect`), and the defect lies strictly between `−r/2` and `r/2`
(`abs_stickelbergerDefect_lt`): each exponent `n_χ` of `χ = ω^{n_χ}` lies in `[1, p − 2]`. For
`r ≤ 3` the only half-integers in that range are `±½`:

* **Exactly half** (`stickelbergerDefect_eq_half_or_neg_half`): a Möbius-signed monomial of length
  at most three — a pair with quadratic product or a triple with trivial product, such as
  `g(χ)g(φ)` for the frame `(3, 6)` or `p·J(χ₁, χ₂)` — has defect `±½` at every place above `p`.
* **The bound is attained** (`stickelbergerPrice_eq_half_mul`): its Stickelberger price at the
  period `k` is exactly `k/2`, and the frame `(k/2, k)` has centre `k/(2(k − 1))`
  (`stickelbergerPrice_div_eq`), which decreases to `½`.

So the arithmetic of Gauss sums alone prices a short Möbius monomial on the line `c = k/2`, with
centres `¾, ⅔, ⅝, ⅗, 7/12, …` at `k = 3, 4, 5, 6, 7, …`. The wall `⅗` of the Gauss pairings is the
point `k = 6` of this line, where it meets their completion bound `c ≥ (2/3)k − 1`
(FCT `two_thirds_mul_period_sub_one_le_pairingC`; `half_mul_le_two_thirds_mul_sub_one_iff`); beyond `k = 6` the price of completing each factor by
its own theta series exceeds the price of the sign.
-/

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger

open GaloisForLFunctions.FamilyContinuationTheory (IsMoebiusSignedTuple)

variable {p : ℕ} [hp : Fact p.Prime]

attribute [local instance] neZero_p neZero_p_sub_one

/-- The defect of `r` nontrivial characters lies strictly between `−r/2` and `r/2`. -/
theorem abs_stickelbergerDefect_lt {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    {L : List (MulChar (ZMod p) (PadicAlgCl p))} (hne : L ≠ []) (hL : ∀ χ ∈ L, χ ≠ 1) :
    |stickelbergerDefect p hζ L| < (L.length : ℝ) / 2 := by
  have hp2 := hp.out.two_le
  have hN : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < p - 1 by omega)
  have hlo : (L.length : ℝ) ≤ ((L.map (teichExp p)).sum : ℝ) := by
    have : L.length ≤ (L.map (teichExp p)).sum := by
      have h := List.sum_le_sum (l := L) (f := fun _ => 1) (g := teichExp p)
        fun χ _ => (teichExp_spec p χ).1
      simpa using h
    exact_mod_cast this
  have hhi : ((L.map (teichExp p)).sum : ℝ) ≤ L.length * ((p - 1 : ℕ) - 1 : ℝ) := by
    have : (L.map (teichExp p)).sum ≤ L.length * (p - 1 - 1) := by
      have h := List.sum_le_sum (l := L) (f := teichExp p) (g := fun _ => p - 1 - 1)
        fun χ hχ => by have := teichExp_lt_of_ne_one p (hL χ hχ); omega
      simpa using h
    have h1 : ((p - 1 - 1 : ℕ) : ℝ) = ((p - 1 : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    calc ((L.map (teichExp p)).sum : ℝ) ≤ ((L.length * (p - 1 - 1) : ℕ) : ℝ) := by exact_mod_cast this
      _ = L.length * ((p - 1 : ℕ) - 1 : ℝ) := by push_cast [h1]; ring
  have hr : (0 : ℝ) < L.length := by
    have : 0 < L.length := List.length_pos_iff.2 hne
    exact_mod_cast this
  rw [stickelbergerDefect_eq, abs_lt]
  constructor
  · have : (L.length : ℝ) / ((p - 1 : ℕ) : ℝ) ≤ ((L.map (teichExp p)).sum : ℝ) / ((p - 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hlo hN.le
    have h0 : 0 < (L.length : ℝ) / ((p - 1 : ℕ) : ℝ) := div_pos hr hN
    linarith
  · have : ((L.map (teichExp p)).sum : ℝ) / ((p - 1 : ℕ) : ℝ) < L.length := by
      rw [div_lt_iff₀ hN]
      nlinarith
    linarith

/-- **A short Möbius monomial pays exactly half at every place.** -/
theorem stickelbergerDefect_eq_half_or_neg_half {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    {L : List (MulChar (ZMod p) (PadicAlgCl p))} (hM : IsMoebiusSignedTuple L)
    (hlen : L.length ≤ 3) :
    stickelbergerDefect p hζ L = 1 / 2 ∨ stickelbergerDefect p hζ L = -(1 / 2) := by
  have hL : ∀ χ ∈ L, χ ≠ 1 := fun χ hχ h1 => by
    have := hM.two_le_order χ hχ
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨j, hj⟩ := (isMoebiusSignedTuple_iff_defect hζ hM.nonempty hL hM.prod_sq_eq_one).1 hM
  have hlt := abs_stickelbergerDefect_lt hζ hM.nonempty hL
  rw [hj, abs_lt] at hlt
  have hr : (L.length : ℝ) ≤ 3 := by exact_mod_cast hlen
  have h1 : (j : ℝ) < 1 := by linarith
  have h2 : (-2 : ℝ) < j := by linarith
  have hj1 : j < 1 := by exact_mod_cast h1
  have hj2 : -2 < j := by exact_mod_cast h2
  rcases (show j = 0 ∨ j = -1 by omega) with rfl | rfl
  · left; rw [hj]; norm_num
  · right; rw [hj]; norm_num

/-- **The bound of the sign is attained**: the Stickelberger price of a Möbius-signed monomial of
length at most three is exactly `k/2`. -/
theorem stickelbergerPrice_eq_half_mul {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) (k : ℝ)
    {L : List (MulChar (ZMod p) (PadicAlgCl p))} (hM : IsMoebiusSignedTuple L)
    (hlen : L.length ≤ 3) : stickelbergerPrice hζ k L = k / 2 := by
  have hp2 : p ≠ 2 := by
    intro h2
    have hL : ∀ χ ∈ L, χ ≠ 1 := fun χ hχ h1 => by
      have := hM.two_le_order χ hχ
      rw [h1, orderOf_one] at this
      omega
    obtain ⟨χ, hχ⟩ := List.exists_mem_of_ne_nil L hM.nonempty
    have := teichExp_lt_of_ne_one p (hL χ hχ)
    have := (teichExp_spec p χ).1
    omega
  have hsup : Finset.univ.sup' Finset.univ_nonempty (fun t : (ZMod (p - 1))ˣ =>
      stickelbergerDefect p hζ (conjList p t L)) = 1 / 2 := by
    refine le_antisymm (Finset.sup'_le _ _ fun t _ => ?_) ?_
    · have hMt := isMoebiusSignedTuple_conjList hp2 hM t
      have hlt : (conjList p t L).length ≤ 3 := by rw [conjList, List.length_map]; exact hlen
      rcases stickelbergerDefect_eq_half_or_neg_half hζ hMt hlt with h | h
      · rw [h]
      · rw [h]; norm_num
    · obtain ⟨t, ht⟩ := exists_conjList_half_le_stickelbergerDefect hζ hM
      exact ht.trans (Finset.le_sup' (fun t : (ZMod (p - 1))ˣ =>
        stickelbergerDefect p hζ (conjList p t L)) (Finset.mem_univ t))
  rw [stickelbergerPrice, hsup]
  ring

/-- The centre of the frame priced by a short Möbius monomial is `k/(2(k − 1))`. -/
theorem stickelbergerPrice_div_eq {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) (k : ℝ)
    {L : List (MulChar (ZMod p) (PadicAlgCl p))} (hM : IsMoebiusSignedTuple L)
    (hlen : L.length ≤ 3) : stickelbergerPrice hζ k L / (k - 1) = k / (2 * (k - 1)) := by
  rw [stickelbergerPrice_eq_half_mul hζ k hM hlen, div_div]

/-- The line `c = k/2` of the sign lies on or below the completion bound `c ≥ (2/3)k − 1` of the
Gauss pairings exactly up to the period `6`, where both give the centre `⅗`. -/
theorem half_mul_le_two_thirds_mul_sub_one_iff (k : ℝ) : k / 2 ≤ 2 / 3 * k - 1 ↔ 6 ≤ k := by
  constructor <;> intro h <;> linarith

#print axioms stickelbergerPrice_eq_half_mul

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger
