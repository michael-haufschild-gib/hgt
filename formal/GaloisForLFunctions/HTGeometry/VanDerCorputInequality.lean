/-
The van der Corput averaging identity and shift bound.

For a sequence supported on `[0, N)` and any `H ≥ 1`, summing the `H`-term block sums over all
block positions `k ∈ [-H+1, N)` counts each term exactly `H` times:

    Σ_{k = -H+1}^{N-1} Σ_{j < H} z (k + j)  =  H · Σ_{k = 0}^{N-1} z k.

Cauchy-Schwarz over the `N + H - 1` block positions then gives

    H² ‖Σ z‖²  ≤  (N + H - 1) · Σ_k ‖blockSum z H k‖²,

which is the inequality behind the `A` process: the free parameter `H` converts a bound on the
differenced sums into a bound on the original sum, and optimising over `H` is what the exponent-pair
calculus records.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities

namespace HTGeometry

open Finset Complex

/-- The block sum of `H` consecutive terms starting at `k`. -/
noncomputable def blockSum (z : ℤ → ℂ) (H : ℕ) (k : ℤ) : ℂ :=
  ∑ j ∈ range H, z (k + j)

/-- Translating the index set of a sum over an integer interval. -/
theorem sum_Ico_shift (z : ℤ → ℂ) (a b c : ℤ) :
    ∑ k ∈ Finset.Ico a b, z (k + c) = ∑ m ∈ Finset.Ico (a + c) (b + c), z m := by
  rw [← Finset.map_add_right_Ico a b c, Finset.sum_map]
  rfl

/-- **The averaging identity.**  For a sequence vanishing outside `[0, N)`, summing the block sums
over all block positions counts each term exactly `H` times. -/
theorem sum_blockSum_eq (z : ℤ → ℂ) (N H : ℕ)
    (hsupp : ∀ k : ℤ, k ∉ Finset.Ico (0 : ℤ) (N : ℤ) → z k = 0) :
    ∑ k ∈ Finset.Ico (-(H : ℤ) + 1) (N : ℤ), blockSum z H k
      = (H : ℂ) * ∑ k ∈ Finset.Ico (0 : ℤ) (N : ℤ), z k := by
  classical
  unfold blockSum
  rw [Finset.sum_comm]
  have key : ∀ j ∈ range H,
      ∑ k ∈ Finset.Ico (-(H : ℤ) + 1) (N : ℤ), z (k + j)
        = ∑ k ∈ Finset.Ico (0 : ℤ) (N : ℤ), z k := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [sum_Ico_shift]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro m hm
      simp only [Finset.mem_Ico] at hm ⊢
      constructor
      · have : (-(H : ℤ) + 1 + j) ≤ 0 := by
          have : (j : ℤ) + 1 ≤ (H : ℤ) := by exact_mod_cast hj
          omega
        omega
      · have : (0 : ℤ) ≤ j := Int.natCast_nonneg j
        omega
    · intro m _ hm
      exact hsupp m hm
  rw [Finset.sum_congr rfl key, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Cauchy-Schwarz over the block positions.**  The squared modulus of a sum of `M` complex
numbers is at most `M` times the sum of their squared moduli. -/
theorem normSq_sum_le_card_mul (s : Finset ℤ) (w : ℤ → ℂ) :
    (‖∑ k ∈ s, w k‖ : ℝ)^2 ≤ (s.card : ℝ) * ∑ k ∈ s, (‖w k‖ : ℝ)^2 := by
  classical
  have h1 : (‖∑ k ∈ s, w k‖ : ℝ) ≤ ∑ k ∈ s, ‖w k‖ := norm_sum_le _ _
  have h2 : (∑ k ∈ s, ‖w k‖)^2 ≤ (s.card : ℝ) * ∑ k ∈ s, (‖w k‖ : ℝ)^2 :=
    sq_sum_le_card_mul_sum_sq
  have h0 : (0:ℝ) ≤ ‖∑ k ∈ s, w k‖ := norm_nonneg _
  nlinarith [h1, h2, h0, Finset.sum_nonneg (fun k (_ : k ∈ s) => norm_nonneg (w k))]

/-- **The van der Corput shift inequality.**  For a sequence supported on `[0,N)` and any `H ≥ 1`,

    H² ‖Σ z‖² ≤ (N + H - 1) · Σ_k ‖blockSum z H k‖².

The right-hand side is the block-energy; expanding it produces the differenced sums, which is why a
bound on the correlations bounds the original sum. -/
theorem vanDerCorput_shift_inequality (z : ℤ → ℂ) (N H : ℕ)
    (hsupp : ∀ k : ℤ, k ∉ Finset.Ico (0 : ℤ) (N : ℤ) → z k = 0) :
    (H : ℝ)^2 * (‖∑ k ∈ Finset.Ico (0 : ℤ) (N : ℤ), z k‖ : ℝ)^2
      ≤ ((Finset.Ico (-(H : ℤ) + 1) (N : ℤ)).card : ℝ)
        * ∑ k ∈ Finset.Ico (-(H : ℤ) + 1) (N : ℤ), (‖blockSum z H k‖ : ℝ)^2 := by
  have hid := sum_blockSum_eq z N H hsupp
  have h1 : (‖∑ k ∈ Finset.Ico (-(H : ℤ) + 1) (N : ℤ), blockSum z H k‖ : ℝ)^2
      = (H : ℝ)^2 * (‖∑ k ∈ Finset.Ico (0 : ℤ) (N : ℤ), z k‖ : ℝ)^2 := by
    rw [hid, norm_mul, mul_pow]
    congr 1
    simp
  rw [← h1]
  exact normSq_sum_le_card_mul _ _

/-- The number of block positions is `N + H - 1`. -/
theorem card_blockPositions (N H : ℕ) (hH : 0 < H) :
    (Finset.Ico (-(H : ℤ) + 1) (N : ℤ)).card = N + H - 1 := by
  rw [Int.card_Ico]
  omega

/-- The correlation of the sequence with its own shift by `h`. -/
noncomputable def corr (z : ℤ → ℂ) (N : ℕ) (h : ℤ) : ℂ :=
  ∑ m ∈ Finset.Ico (0 : ℤ) (N : ℤ), z (m + h) * (starRingEnd ℂ) (z m)

/-- The squared modulus of a block sum, expanded over pairs of offsets. -/
theorem normSq_blockSum_eq (z : ℤ → ℂ) (H : ℕ) (k : ℤ) :
    ((‖blockSum z H k‖ : ℝ)^2 : ℂ)
      = ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, z (k + j₁) * (starRingEnd ℂ) (z (k + j₂)) := by
  have h1 : ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, z (k + j₁) * (starRingEnd ℂ) (z (k + j₂))
      = blockSum z H k * (starRingEnd ℂ) (blockSum z H k) := by
    unfold blockSum
    rw [map_sum, Finset.sum_mul_sum]
  rw [h1, Complex.mul_conj]
  norm_cast
  exact Complex.sq_norm _

/-- **The block energy is a sum of correlations.**  Summing the squared block sums over all block
positions and reindexing by `m = k + j₂` turns the energy into a double sum of shift correlations,
one for each ordered pair of offsets. -/
theorem sum_blockEnergy_eq_corrSum (z : ℤ → ℂ) (N H : ℕ)
    (hsupp : ∀ k : ℤ, k ∉ Finset.Ico (0 : ℤ) (N : ℤ) → z k = 0) :
    ((∑ k ∈ Finset.Ico (-(H : ℤ) + 1) (N : ℤ), (‖blockSum z H k‖ : ℝ)^2 : ℝ) : ℂ)
      = ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, corr z N ((j₁ : ℤ) - (j₂ : ℤ)) := by
  classical
  push_cast
  rw [Finset.sum_congr rfl (fun k _ => normSq_blockSum_eq z H k)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j₂ hj₂ => ?_
  rw [Finset.mem_range] at hj₁ hj₂
  unfold corr
  have hshift : ∑ k ∈ Finset.Ico (-(H : ℤ) + 1) (N : ℤ),
        z (k + j₁) * (starRingEnd ℂ) (z (k + j₂))
      = ∑ m ∈ Finset.Ico (-(H : ℤ) + 1 + j₂) ((N : ℤ) + j₂),
        z (m + ((j₁ : ℤ) - (j₂ : ℤ))) * (starRingEnd ℂ) (z m) := by
    rw [← sum_Ico_shift (fun m => z (m + ((j₁ : ℤ) - (j₂ : ℤ))) * (starRingEnd ℂ) (z m))
      (-(H : ℤ) + 1) (N : ℤ) (j₂)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    ring
  rw [hshift]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro m hm
    simp only [Finset.mem_Ico] at hm ⊢
    have h1 : (j₁ : ℤ) + 1 ≤ (H : ℤ) := by exact_mod_cast hj₁
    have h2 : (j₂ : ℤ) + 1 ≤ (H : ℤ) := by exact_mod_cast hj₂
    have h3 : (0 : ℤ) ≤ (j₂ : ℤ) := Int.natCast_nonneg j₂
    omega
  · intro m _ hm
    rw [hsupp m hm]
    simp

/-- **The offset-pair count.**  The number of ordered pairs of offsets in `[0,H)` whose difference
is `h` is `H - |h|`; this is the triangular weight in the van der Corput inequality. -/
theorem card_offsetPairs (H : ℕ) (h : ℤ) :
    (((range H) ×ˢ (range H)).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = h)).card
      = (H - h.natAbs) := by
  classical
  rw [show (H - h.natAbs) = (range (H - h.natAbs)).card from (Finset.card_range _).symm]
  rcases le_or_gt 0 h with hh | hh
  · lift h to ℕ using hh with d
    rw [Int.natAbs_natCast]
    refine Finset.card_nbij' (i := fun p => p.2) (j := fun j => (j + d, j)) ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_range] at hp
      obtain ⟨⟨ha, _hb⟩, hab⟩ := hp
      refine Finset.mem_coe.mpr (Finset.mem_range.mpr ?_)
      show p.2 < H - d
      have hpd : p.1 = p.2 + d := by omega
      omega
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_range] at hj
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩)
      · exact Finset.mem_range.mpr (show j + d < H by omega)
      · exact Finset.mem_range.mpr (show j < H by omega)
      · show ((j + d : ℕ) : ℤ) - (j : ℤ) = (d : ℤ)
        push_cast; ring
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_range] at hp
      obtain ⟨⟨_ha, _hb⟩, hab⟩ := hp
      have hpd : p.2 + d = p.1 := by omega
      exact Prod.ext hpd rfl
    · intro j _; rfl
  · have habs : (h.natAbs : ℤ) = -h := Int.ofNat_natAbs_of_nonpos (le_of_lt hh)
    refine Finset.card_nbij' (i := fun p => p.1) (j := fun j => (j, j + h.natAbs)) ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_range] at hp
      obtain ⟨⟨_ha, hb⟩, hab⟩ := hp
      refine Finset.mem_coe.mpr (Finset.mem_range.mpr ?_)
      show p.1 < H - h.natAbs
      have hz : (p.2 : ℤ) = (p.1 : ℤ) + (h.natAbs : ℤ) := by omega
      have hpd : p.2 = p.1 + h.natAbs := by exact_mod_cast hz
      omega
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_range] at hj
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩)
      · exact Finset.mem_range.mpr (lt_of_lt_of_le hj (Nat.sub_le H h.natAbs))
      · exact Finset.mem_range.mpr (Nat.add_lt_of_lt_sub hj)
      · show (j : ℤ) - ((j + h.natAbs : ℕ) : ℤ) = h
        push_cast
        rw [abs_of_neg hh]
        ring
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_range] at hp
      obtain ⟨⟨_ha, _hb⟩, hab⟩ := hp
      have hz : (p.2 : ℤ) = (p.1 : ℤ) + (h.natAbs : ℤ) := by omega
      have hpd : p.2 = p.1 + h.natAbs := by exact_mod_cast hz
      exact Prod.ext rfl hpd.symm
    · intro j _; rfl

/-- **The van der Corput inequality, correlation form.**  For a sequence supported on `[0,N)` and
any `H`,

    H² ‖Σ z‖²  ≤  (N + H - 1) · Σ_{j₁,j₂ < H} ‖corr z N (j₁ - j₂)‖.

A bound on the shift correlations therefore bounds the original sum, with the free parameter `H`
trading the number of correlations against the block count.  This is the analytic content that the
exponent-pair `A` process records. -/
theorem vanDerCorput_correlation_bound (z : ℤ → ℂ) (N H : ℕ) (hH : 0 < H)
    (hsupp : ∀ k : ℤ, k ∉ Finset.Ico (0 : ℤ) (N : ℤ) → z k = 0) :
    (H : ℝ)^2 * (‖∑ k ∈ Finset.Ico (0 : ℤ) (N : ℤ), z k‖ : ℝ)^2
      ≤ ((N : ℝ) + H - 1) * ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ := by
  classical
  set E : ℝ := ∑ k ∈ Finset.Ico (-(H : ℤ) + 1) (N : ℤ), (‖blockSum z H k‖ : ℝ)^2 with hE
  have hEnn : 0 ≤ E := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hEbound : E ≤ ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ := by
    have hcast : (E : ℂ) = ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, corr z N ((j₁ : ℤ) - (j₂ : ℤ)) :=
      sum_blockEnergy_eq_corrSum z N H hsupp
    have h1 : (E : ℝ) = ‖(E : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hEnn]
    calc E = ‖(E : ℂ)‖ := h1
      _ = ‖∑ j₁ ∈ range H, ∑ j₂ ∈ range H, corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ := by rw [hcast]
      _ ≤ ∑ j₁ ∈ range H, ‖∑ j₂ ∈ range H, corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ := norm_sum_le _ _
      _ ≤ ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ :=
          Finset.sum_le_sum fun j₁ _ => norm_sum_le _ _
  have hcard : ((Finset.Ico (-(H : ℤ) + 1) (N : ℤ)).card : ℝ) ≤ (N : ℝ) + H - 1 := by
    rw [Int.card_Ico]
    have : ((N : ℤ) - (-(H : ℤ) + 1)).toNat ≤ N + H - 1 := by omega
    calc (((N : ℤ) - (-(H : ℤ) + 1)).toNat : ℝ) ≤ ((N + H - 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ (N : ℝ) + H - 1 := by
          have h1 : (1 : ℕ) ≤ H := hH
          push_cast [Nat.cast_sub (by omega : 1 ≤ N + H)]
          linarith
  have hstep := vanDerCorput_shift_inequality z N H hsupp
  have hnn : (0 : ℝ) ≤ ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcardnn : (0 : ℝ) ≤ ((Finset.Ico (-(H : ℤ) + 1) (N : ℤ)).card : ℝ) := Nat.cast_nonneg _
  calc (H : ℝ)^2 * (‖∑ k ∈ Finset.Ico (0 : ℤ) (N : ℤ), z k‖ : ℝ)^2
      ≤ ((Finset.Ico (-(H : ℤ) + 1) (N : ℤ)).card : ℝ) * E := hstep
    _ ≤ ((N : ℝ) + H - 1) * ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ := by
        have h2 : ((Finset.Ico (-(H : ℤ) + 1) (N : ℤ)).card : ℝ) * E
            ≤ ((Finset.Ico (-(H : ℤ) + 1) (N : ℤ)).card : ℝ)
              * ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ :=
          mul_le_mul_of_nonneg_left hEbound hcardnn
        have h3 : ((Finset.Ico (-(H : ℤ) + 1) (N : ℤ)).card : ℝ)
              * ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖
            ≤ ((N : ℝ) + H - 1)
              * ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ :=
          mul_le_mul_of_nonneg_right hcard hnn
        linarith


/-!
### The information-theoretic floor of the method

The diagonal shift contributes `corr z N 0 = Σ_{m<N} ‖z m‖²`, which for a unimodular sequence is
exactly `N`, and it appears `H` times in the offset-pair sum (once for each `j₁ = j₂`).  So whatever
the off-diagonal correlations do, the right-hand side of the correlation bound is at least
`(N + H - 1)·H·N`, and dividing by `H²` gives

    ‖Σ z‖²  ≤  (N + H - 1)·N/H  ≥  N.

**No choice of `H` lets the van der Corput inequality prove better than square-root cancellation.**
That ceiling is exactly the Lindelöf hypothesis for the critical block, so the method's failure to
prove LH is due entirely to the off-diagonal correlations, never to the diagonal.
-/

/-- The diagonal correlation of a unimodular sequence supported on `[0,N)` is `N`. -/
theorem corr_zero_of_unimodular (z : ℤ → ℂ) (N : ℕ)
    (hz : ∀ k ∈ Finset.Ico (0 : ℤ) (N : ℤ), ‖z k‖ = 1) :
    corr z N 0 = (N : ℂ) := by
  unfold corr
  have hterm : ∀ m ∈ Finset.Ico (0 : ℤ) (N : ℤ),
      z (m + 0) * (starRingEnd ℂ) (z m) = 1 := by
    intro m hm
    rw [add_zero, Complex.mul_conj]
    have hnorm : ‖z m‖ = 1 := hz m hm
    rw [← Complex.sq_norm, hnorm]
    norm_num
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Int.card_Ico]
  simp

/-- **The diagonal share of the offset-pair sum.**  The `H` pairs with `j₁ = j₂` contribute
`H·‖corr z N 0‖`, so the offset-pair sum is at least that. -/
theorem diagonal_le_offsetPairSum (z : ℤ → ℂ) (N H : ℕ) :
    (H : ℝ) * ‖corr z N 0‖
      ≤ ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ := by
  classical
  have hdiag : ∀ j₁ ∈ range H,
      ‖corr z N 0‖ ≤ ∑ j₂ ∈ range H, ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ := by
    intro j₁ hj₁
    have h := Finset.single_le_sum (f := fun j₂ : ℕ => ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖)
      (fun j _ => norm_nonneg _) hj₁
    simpa using h
  calc (H : ℝ) * ‖corr z N 0‖ = ∑ _j₁ ∈ range H, ‖corr z N 0‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ :=
        Finset.sum_le_sum hdiag

/-- **The floor of the method.**  For a unimodular sequence, the bound delivered by
`vanDerCorput_correlation_bound` is never smaller than `N`: square-root cancellation is the absolute
ceiling of the van der Corput inequality, whatever `H` is chosen and whatever the off-diagonal
correlations are. -/
theorem vanDerCorput_bound_ge_length (z : ℤ → ℂ) (N H : ℕ) (hN : 1 ≤ N) (hH : 0 < H)
    (hz : ∀ k ∈ Finset.Ico (0 : ℤ) (N : ℤ), ‖z k‖ = 1) :
    (N : ℝ)
      ≤ ((N : ℝ) + H - 1) / (H : ℝ)^2
        * ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ := by
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcorr0 : ‖corr z N 0‖ = (N : ℝ) := by
    rw [corr_zero_of_unimodular z N hz]
    simp
  have hdiag := diagonal_le_offsetPairSum z N H
  rw [hcorr0] at hdiag
  have hfac : (0 : ℝ) < ((N : ℝ) + H - 1) / (H : ℝ)^2 := by
    have : (0 : ℝ) < (N : ℝ) + H - 1 := by linarith
    positivity
  calc (N : ℝ) = ((N : ℝ) + H - 1) / (H : ℝ)^2 * ((H : ℝ) * (N : ℝ))
        - (((N : ℝ) - 1) / (H : ℝ)) * (N : ℝ) := by
        field_simp
        ring
    _ ≤ ((N : ℝ) + H - 1) / (H : ℝ)^2 * ((H : ℝ) * (N : ℝ)) := by
        have : (0 : ℝ) ≤ (((N : ℝ) - 1) / (H : ℝ)) * (N : ℝ) := by
          have h1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
          positivity
        linarith
    _ ≤ ((N : ℝ) + H - 1) / (H : ℝ)^2
          * ∑ j₁ ∈ range H, ∑ j₂ ∈ range H, ‖corr z N ((j₁ : ℤ) - (j₂ : ℤ))‖ :=
        mul_le_mul_of_nonneg_left hdiag (le_of_lt hfac)

end HTGeometry
