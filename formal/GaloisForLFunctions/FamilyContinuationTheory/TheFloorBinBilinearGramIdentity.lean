import GaloisForLFunctions.FamilyContinuationTheory.TheBudgetInTheTwistExponent

/-!
# The floor-bin bilinear signed Gram identity and its phase transition

In the twist-exponent budget (`endpointExponentOrder_floor_bin_pos_of_lt`), bounding the floor bin
(`δ = 0`, rows `u ∈ B₀` without zeros right of `½`) by the triangle inequality sets `R = 1` and
creates the universal barrier `θ ≥ (5n − 8)/(5(n − 1))` (`22/25` at `n = 6`, `σ₀ = 13/15`).
Interchanging the row and column sums before taking absolute values replaces `R = 1` by a
Hermitian row-to-row Gram quadratic form preserving all relative phases `α(u₁) conj(α(u₂))` across
distinct floor-bin rows:

* **Exact bilinear signed Gram identity** (`sum_norm_sq_eq_diag_add_offDiag`,
  `norm_sq_bilinearFloorSum_le_mul_signedGram`). For any finite floor-bin set `B₀`, column shell
  `M`, row amplitudes `α : B₀ → ℂ`, column weights `b : M → ℂ`, and pairing `Φ : B₀ → M → ℂ`,
  `‖∑_{u ∈ B₀} α(u) ∑_{m ∈ M} b(m) Φ(u, m)‖² ≤ (∑_m ‖b(m)‖²) Q_M(α)` where
  `Q_M(α) = ∑_u ‖α(u)‖² G_M(u, u) + Re ∑_{u₁} ∑_{u₂ ≠ u₁} α(u₁) conj(α(u₂)) G_M(u₁, u₂)` and
  `G_M(u₁, u₂) = ∑_m Φ(u₁, m) conj(Φ(u₂, m))`.
* **Phase-blind saturation and polynomial-completion obstructions**
  (`exists_matched_phase_saturation`, `norm_sq_bilinearFloorSum_addChar_le`,
  `le_max_approxRem_approxComplete`). Unimodular matched phases `α(u) = A₀ conj(Φ(u, m₀))` force
  `Q_M(α) ≥ |B₀|² A₀²`; enlarging `B₀ ⊆ AddChar G ℂ` to the full character group gives
  `|B₀| |G| A₀² ∑_x ‖b(x)‖²` (`R₀ = 1` at `|B₀| ≍ |G|`); and approximating `L⁻¹` on
  `Re s = ½ + α₁` by a polynomial of length `Z^ρ` before completing `u` obeys the convex identity
  `(1 − α₁) E_rem + α₁ E_complete = E_tri + α₁(lx + ly − ℓ) ≥ E_tri` whenever `ℓ ≤ lx + ly`.
* **Two-lock decomposition and near-floor continuum spillover**
  (`endpointExponentOrder_balanced_edge_spillover`, `zeroDensityTheta_balanced_barrier`,
  `endpointExponentOrder_sqrt_cancellation_nonpos`). On the balanced edge `lx = ly = (1 − ℓ)/2` at
  `q = δ/2`, the high exponent equals `(5ℓ − 1)/4 + ((1 + 3ℓ)/2)(R − (1 − δ))` independently of
  `n`. Zero-density excess `R = 1 − δ + η` interpolates `((5 + 6η)n − 8)/((5 + 6η)(n − 1))` across
  `[22/25, 9/10]`, while crossing `< 22/25` (`ℓ > 1/5`) requires uniform cancellation
  `R ≤ (3 + ℓ)/(2(1 + 3ℓ)) − δ`, satisfied by `R = (1 − δ)/2` down to `(n − 2)/(n − 1)` for all
  `2 ≤ n ≤ 6`.
* **Global two-phase signed-Gram bifurcation** (`endpointExponentOrder_signedGram_pos_of_lt`,
  `endpointExponentOrder_signedGram_broken_pos_of_lt`). Under floor-bin exponent `R₀ ∈ [½, 1]`,
  the global minimum of `probeThetaGen` transitions at `R_crit(n) = ½ + 1/n` from the symmetric
  balanced curve `((6 R₀ − 1)n − 8)/((6 R₀ − 1)(n − 1))` (`R₀ ∈ [½ + 1/n, 1]`, hitting
  `(n − 2)/(n − 1)` at `R₀ = 5/6`) to the `lx = 0` boundary curve `signedGramBrokenTheta n R₀`
  (`R₀ ∈ [½, ½ + 1/n]`, `n ≥ 3`).
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.Budget

open Finset ComplexConjugate

noncomputable section

/-! ### Finite-dimensional bilinear signed Gram identity -/

/-- Bilinear floor-bin sum pairing row amplitudes `α : B₀ → ℂ` with column sums
`∑ m, b m * Φ u m`. -/
def bilinearFloorSum {B₀ M : Type*} [Fintype B₀] [Fintype M]
    (Φ : B₀ → M → ℂ) (α : B₀ → ℂ) (b : M → ℂ) : ℂ :=
  ∑ u : B₀, α u * ∑ m : M, b m * Φ u m

/-- Row-to-row Hermitian Gram kernel `G_M(u₁, u₂) = ∑ m, Φ(u₁, m) conj(Φ(u₂, m))` induced by the
column shell `M`. -/
def rowGramMatrix {B₀ M : Type*} [Fintype M] (Φ : B₀ → M → ℂ) (u₁ u₂ : B₀) : ℂ :=
  ∑ m : M, Φ u₁ m * conj (Φ u₂ m)

/-- Signed off-diagonal row correlation sum preserving relative phases `α(u₁) conj(α(u₂))` across
distinct floor-bin rows `u₁ ≠ u₂`. -/
def signedGramOffDiag {B₀ M : Type*} [Fintype B₀] [DecidableEq B₀] [Fintype M]
    (Φ : B₀ → M → ℂ) (α : B₀ → ℂ) : ℂ :=
  ∑ u₁ : B₀, ∑ u₂ ∈ Finset.univ.erase u₁, α u₁ * conj (α u₂) * rowGramMatrix Φ u₁ u₂

theorem rowGramMatrix_conj_symm {B₀ M : Type*} [Fintype M] (Φ : B₀ → M → ℂ) (u₁ u₂ : B₀) :
    conj (rowGramMatrix Φ u₁ u₂) = rowGramMatrix Φ u₂ u₁ := by
  unfold rowGramMatrix
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply, mul_comm]

theorem rowGramMatrix_diag_eq {B₀ M : Type*} [Fintype M] (Φ : B₀ → M → ℂ) (u : B₀) :
    rowGramMatrix Φ u u = ∑ m : M, ((‖Φ u m‖ ^ 2 : ℝ) : ℂ) := by
  unfold rowGramMatrix
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem bilinearFloorSum_eq_column_sum {B₀ M : Type*} [Fintype B₀] [Fintype M]
    (Φ : B₀ → M → ℂ) (α : B₀ → ℂ) (b : M → ℂ) :
    bilinearFloorSum Φ α b = ∑ m : M, b m * ∑ u : B₀, α u * Φ u m := by
  unfold bilinearFloorSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => by ring

/-- **Complex signed Gram expansion.** Expanding the dual column `ℓ²` norm of `∑ u, α(u) Φ(u, m)`
gives the full row-to-row Hermitian Gram form. -/
theorem sum_mul_conj_eq_rowGramMatrix {B₀ M : Type*} [Fintype B₀] [Fintype M]
    (Φ : B₀ → M → ℂ) (α : B₀ → ℂ) :
    ∑ m : M, ((‖∑ u : B₀, α u * Φ u m‖ ^ 2 : ℝ) : ℂ) =
      ∑ u₁ : B₀, ∑ u₂ : B₀, α u₁ * conj (α u₂) * rowGramMatrix Φ u₁ u₂ := by
  have hnorm : ∀ m : M, ((‖∑ u : B₀, α u * Φ u m‖ ^ 2 : ℝ) : ℂ) =
      ∑ u₁ : B₀, ∑ u₂ : B₀, α u₁ * conj (α u₂) * (Φ u₁ m * conj (Φ u₂ m)) := by
    intro m
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun u₁ _ => Finset.sum_congr rfl fun u₂ _ => ?_
    rw [map_mul]
    ring
  simp_rw [hnorm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u₂ _ => ?_
  rw [← Finset.mul_sum]
  rfl

/-- **Real diagonal-plus-signed-off-diagonal Gram identity.** The dual column `ℓ²` norm splits
into the nonnegative diagonal plus the real part of the signed off-diagonal row correlation. -/
theorem sum_norm_sq_eq_diag_add_offDiag {B₀ M : Type*} [Fintype B₀] [DecidableEq B₀] [Fintype M]
    (Φ : B₀ → M → ℂ) (α : B₀ → ℂ) :
    ∑ m : M, ‖∑ u : B₀, α u * Φ u m‖ ^ 2 =
      (∑ u : B₀, ‖α u‖ ^ 2 * ∑ m : M, ‖Φ u m‖ ^ 2) + (signedGramOffDiag Φ α).re := by
  have hc := congrArg Complex.re (sum_mul_conj_eq_rowGramMatrix Φ α)
  rw [Complex.re_sum] at hc
  simp only [Complex.ofReal_re] at hc
  rw [hc]
  have hsplit : ∑ u₁ : B₀, ∑ u₂ : B₀, α u₁ * conj (α u₂) * rowGramMatrix Φ u₁ u₂ =
      (∑ u : B₀, α u * conj (α u) * rowGramMatrix Φ u u) + signedGramOffDiag Φ α := by
    unfold signedGramOffDiag
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u₁ _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u₁)]
  rw [hsplit, Complex.add_re]
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, rowGramMatrix_diag_eq, ← Complex.ofReal_sum,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Bilinear signed Gram bound.** Cauchy–Schwarz over the column shell `M` bounds
`‖bilinearFloorSum Φ α b‖²` by `(∑_m ‖b(m)‖²)` times the exact signed Gram form, preserving all
off-diagonal phase cancellations across floor-bin rows `u₁ ≠ u₂`. -/
theorem norm_sq_bilinearFloorSum_le_mul_signedGram {B₀ M : Type*} [Fintype B₀] [DecidableEq B₀]
    [Fintype M] (Φ : B₀ → M → ℂ) (α : B₀ → ℂ) (b : M → ℂ) :
    ‖bilinearFloorSum Φ α b‖ ^ 2 ≤
      (∑ m : M, ‖b m‖ ^ 2) *
        ((∑ u : B₀, ‖α u‖ ^ 2 * ∑ m : M, ‖Φ u m‖ ^ 2) + (signedGramOffDiag Φ α).re) := by
  rw [← sum_norm_sq_eq_diag_add_offDiag, bilinearFloorSum_eq_column_sum]
  have htri : ‖∑ m : M, b m * ∑ u : B₀, α u * Φ u m‖ ≤
      ∑ m : M, ‖b m‖ * ‖∑ u : B₀, α u * Φ u m‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_mul]
  have hsq : ‖∑ m : M, b m * ∑ u : B₀, α u * Φ u m‖ ^ 2 ≤
      (∑ m : M, ‖b m‖ * ‖∑ u : B₀, α u * Φ u m‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  exact hsq.trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun m => ‖b m‖) (fun m => ‖∑ u : B₀, α u * Φ u m‖))

/-! ### Phase-blind saturation and polynomial-completion obstructions -/

/-- For any unimodular pairing `‖Φ(u, m₀)‖ = 1` at a column `m₀ ∈ M`, matched phases
`α(u) = A₀ conj(Φ(u, m₀))` satisfy `‖α(u)‖ = A₀` and saturate the signed Gram form at
`|B₀|² A₀²` (`R₀ = 1`). -/
theorem exists_matched_phase_saturation {B₀ M : Type*} [Fintype B₀] [Fintype M]
    (Φ : B₀ → M → ℂ) (m₀ : M) (hunit : ∀ u : B₀, ‖Φ u m₀‖ = 1) {A₀ : ℝ} (hA₀ : 0 ≤ A₀) :
    ∃ α : B₀ → ℂ, (∀ u : B₀, ‖α u‖ = A₀) ∧
      (Fintype.card B₀ : ℝ) ^ 2 * A₀ ^ 2 ≤ ∑ m : M, ‖∑ u : B₀, α u * Φ u m‖ ^ 2 := by
  refine ⟨fun u => (A₀ : ℂ) * conj (Φ u m₀), fun u => ?_, ?_⟩
  · rw [norm_mul, Complex.norm_of_nonneg hA₀, RCLike.norm_conj, hunit u, mul_one]
  · have hsingle : ‖∑ u : B₀, ((A₀ : ℂ) * conj (Φ u m₀)) * Φ u m₀‖ ^ 2 ≤
        ∑ m : M, ‖∑ u : B₀, ((A₀ : ℂ) * conj (Φ u m₀)) * Φ u m‖ ^ 2 :=
      Finset.single_le_sum (fun m _ => sq_nonneg _) (Finset.mem_univ m₀)
    have heval : ∑ u : B₀, ((A₀ : ℂ) * conj (Φ u m₀)) * Φ u m₀ =
        (Fintype.card B₀ : ℂ) * (A₀ : ℂ) := by
      have hterm : ∀ u : B₀, ((A₀ : ℂ) * conj (Φ u m₀)) * Φ u m₀ = (A₀ : ℂ) := by
        intro u
        rw [mul_assoc, mul_comm (conj (Φ u m₀)), Complex.mul_conj, Complex.normSq_eq_norm_sq,
          hunit u, one_pow, Complex.ofReal_one, mul_one]
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [heval, norm_mul, Complex.norm_natCast, Complex.norm_of_nonneg hA₀, mul_pow] at hsingle
    exact hsingle

/-- Dual orthogonality on a finite additive abelian group `G`: enlarging a floor-bin character set
`B₀ ⊆ AddChar G ℂ` to the full Pontryagin dual bounds `∑_{ψ ∈ B₀} ‖∑_x b(x) ψ(x)‖²` by
`|G| ∑_x ‖b(x)‖²`, so Cauchy–Schwarz on `B₀` gives `|B₀| |G| A₀² ∑_x ‖b(x)‖²` (`R₀ = 1` at
`|B₀| ≍ |G|`). -/
theorem sum_addChar_subset_norm_sq_le {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (B₀ : Finset (AddChar G ℂ)) (b : G → ℂ) :
    ∑ ψ ∈ B₀, ‖∑ x : G, b x * ψ x‖ ^ 2 ≤ (Fintype.card G : ℝ) * ∑ x : G, ‖b x‖ ^ 2 := by
  have hsub : ∑ ψ ∈ B₀, ‖∑ x : G, b x * ψ x‖ ^ 2 ≤
      ∑ ψ : AddChar G ℂ, ‖∑ x : G, b x * ψ x‖ ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg fun ψ => sq_nonneg _
  refine hsub.trans (le_of_eq ?_)
  have horth : ∀ x y : G, ∑ ψ : AddChar G ℂ, ψ x * conj (ψ y) =
      if x = y then (Fintype.card G : ℂ) else 0 := by
    intro x y
    have hconj : ∀ ψ : AddChar G ℂ, ψ x * conj (ψ y) = ψ (x - y) := by
      intro ψ
      have hn : ψ y ^ Fintype.card G = 1 := by
        rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
      have hnorm : ‖ψ y‖ = 1 := norm_eq_one_of_pow_eq_one hn Fintype.card_ne_zero
      have hsq : Complex.normSq (ψ y) = 1 := by rw [Complex.normSq_eq_norm_sq, hnorm, one_pow]
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, Complex.inv_def, hsq]
      simp
    simp_rw [hconj]
    by_cases hxy : x = y
    · subst hxy
      simp [AddChar.card_eq]
    · rw [if_neg hxy]
      have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have hdd : ∑ ψ : AddChar G ℂ, ψ (x - y) =
          ∑ ψ : AddChar G ℂ, (AddChar.doubleDualEmb (x - y) : AddChar (AddChar G ℂ) ℂ) ψ := rfl
      rw [hdd, AddChar.sum_eq_zero_iff_ne_zero.mpr (AddChar.doubleDualEmb_ne_zero.mpr hne)]
  have hc := congrArg Complex.re
    (sum_mul_conj_eq_rowGramMatrix (fun (x : G) (ψ : AddChar G ℂ) => ψ x) b)
  rw [Complex.re_sum] at hc
  simp only [Complex.ofReal_re] at hc
  have hswap : ∀ ψ : AddChar G ℂ, ∑ x : G, b x * ψ x = ∑ x : G, b x * (fun x ψ => ψ x) x ψ :=
    fun _ => rfl
  simp_rw [hswap]
  rw [hc]
  have hdiag : ∑ x : G, ∑ y : G, b x * conj (b y) *
        rowGramMatrix (fun (x : G) (ψ : AddChar G ℂ) => ψ x) x y =
      (Fintype.card G : ℂ) * ∑ x : G, ((‖b x‖ ^ 2 : ℝ) : ℂ) := by
    unfold rowGramMatrix
    simp_rw [horth]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single x]
    · rw [if_pos rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq, mul_comm]
    · intro y _ hyx
      rw [if_neg (Ne.symm hyx), mul_zero]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  rw [hdiag, ← Complex.ofReal_natCast, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
    Complex.ofReal_re]

theorem norm_sq_bilinearFloorSum_addChar_le {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (B₀ : Finset (AddChar G ℂ)) (α : AddChar G ℂ → ℂ) (b : G → ℂ)
    {A₀ : ℝ} (hA₀ : 0 ≤ A₀) (hα : ∀ ψ ∈ B₀, ‖α ψ‖ ≤ A₀) :
    ‖∑ ψ ∈ B₀, α ψ * ∑ x : G, b x * ψ x‖ ^ 2 ≤
      (B₀.card : ℝ) * (Fintype.card G : ℝ) * A₀ ^ 2 * ∑ x : G, ‖b x‖ ^ 2 := by
  have htri : ‖∑ ψ ∈ B₀, α ψ * ∑ x : G, b x * ψ x‖ ≤
      ∑ ψ ∈ B₀, ‖α ψ‖ * ‖∑ x : G, b x * ψ x‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ψ _ => ?_)
    rw [norm_mul]
  have hcs : ‖∑ ψ ∈ B₀, α ψ * ∑ x : G, b x * ψ x‖ ^ 2 ≤
      (∑ ψ ∈ B₀, ‖α ψ‖ ^ 2) * (∑ ψ ∈ B₀, ‖∑ x : G, b x * ψ x‖ ^ 2) :=
    (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq B₀ (fun ψ => ‖α ψ‖) (fun ψ => ‖∑ x : G, b x * ψ x‖))
  have hα_sum : ∑ ψ ∈ B₀, ‖α ψ‖ ^ 2 ≤ (B₀.card : ℝ) * A₀ ^ 2 := by
    calc ∑ ψ ∈ B₀, ‖α ψ‖ ^ 2 ≤ ∑ _ψ ∈ B₀, A₀ ^ 2 :=
          Finset.sum_le_sum fun ψ hψ => pow_le_pow_left₀ (norm_nonneg _) (hα ψ hψ) 2
      _ = (B₀.card : ℝ) * A₀ ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hmul := mul_le_mul hα_sum (sum_addChar_subset_norm_sq_le B₀ b)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
  linarith [hcs, hmul]

/-- Remainder exponent when approximating `L^S(s, η χ_u)⁻¹` on `Re s = ½ + α₁` by a Dirichlet
polynomial of length `Z^ρ`. -/
def approxRemExponent (E_tri α₁ ρ : ℝ) : ℝ := E_tri - α₁ * (ρ - 1)

/-- Complete-sum exponent after extending the `Z^ρ` polynomial from `B₀` to all rows `u` and
dualizing by Poisson summation. -/
def approxCompleteExponent (E_tri lx ly ℓ α₁ ρ : ℝ) : ℝ :=
  E_tri + (lx + ly - ℓ) + (1 - α₁) * (ρ - 1)

/-- **Convex identity for polynomial-approximant completion.** The parameter `ρ` cancels
identically between the remainder and completed-family exponents. -/
theorem approx_convex_combination_eq (E_tri lx ly ℓ α₁ ρ : ℝ) :
    (1 - α₁) * approxRemExponent E_tri α₁ ρ + α₁ * approxCompleteExponent E_tri lx ly ℓ α₁ ρ =
      E_tri + α₁ * (lx + ly - ℓ) := by
  unfold approxRemExponent approxCompleteExponent
  ring

/-- **Polynomial-completion obstruction.** For every line shift `α₁ ∈ [0, 1]` and polynomial
length exponent `ρ ∈ ℝ`, at least one of the remainder and completed-family exponents is at least
the triangle-inequality floor exponent whenever `ℓ ≤ lx + ly`. -/
theorem le_max_approxRem_approxComplete {E_tri lx ly ℓ α₁ : ℝ}
    (hα0 : 0 ≤ α₁) (hα1 : α₁ ≤ 1) (hℓ : ℓ ≤ lx + ly) (ρ : ℝ) :
    E_tri ≤ max (approxRemExponent E_tri α₁ ρ) (approxCompleteExponent E_tri lx ly ℓ α₁ ρ) := by
  have hconv := approx_convex_combination_eq E_tri lx ly ℓ α₁ ρ
  set M₀ := max (approxRemExponent E_tri α₁ ρ) (approxCompleteExponent E_tri lx ly ℓ α₁ ρ)
  have h1 : (1 - α₁) * approxRemExponent E_tri α₁ ρ ≤ (1 - α₁) * M₀ :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
  have h2 : α₁ * approxCompleteExponent E_tri lx ly ℓ α₁ ρ ≤ α₁ * M₀ :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hα0
  have h3 : 0 ≤ α₁ * (lx + ly - ℓ) := mul_nonneg hα0 (by linarith)
  nlinarith

/-! ### Two-lock decomposition inside `[22/25, 9/10]` and near-floor continuum spillover -/

/-- Effective twist threshold on the balanced edge `lx = ly = (1 − ℓ)/2` under zero-density row
count `R(δ) = 1 − δ + η`. -/
def zeroDensityTheta (n η : ℝ) : ℝ := ((5 + 6 * η) * n - 8) / ((5 + 6 * η) * (n - 1))

/-- **Order-independent spillover identity on the balanced edge.** At `lx = ly = (1 − ℓ)/2`,
`σ₀ = 1 − (1 + 3ℓ)/(2n)`, and `q = δ/2`, the order `n` cancels identically out of
`endpointExponentOrder`, leaving `(5ℓ − 1)/4 + ((1 + 3ℓ)/2)(R − (1 − δ))`. -/
theorem endpointExponentOrder_balanced_edge_spillover {n : ℝ} (hn0 : n ≠ 0) (ℓ δ R : ℝ) :
    endpointExponentOrder n ((1 - ℓ) / 2) ((1 - ℓ) / 2) ℓ (1 - (1 + 3 * ℓ) / (2 * n))
        δ (δ / 2) R =
      (5 * ℓ - 1) / 4 + (1 + 3 * ℓ) / 2 * (R - (1 - δ)) := by
  unfold endpointExponentOrder
  field_simp
  ring

/-- `zeroDensityTheta` interpolates continuously from the floor-bin barrier `22/25` (`η = 0`) to
the published `9/10` boundary (`η = 1/18`) at `n = 6`. -/
theorem zeroDensityTheta_six_landmarks :
    zeroDensityTheta 6 0 = 22 / 25 ∧ zeroDensityTheta 6 (1 / 18) = 9 / 10 := by
  norm_num [zeroDensityTheta]

/-- On the balanced edge `M = 1 − ℓ`, any effective twist exponent strictly below
`zeroDensityTheta n η` (`η > −5/6`) forces strictly positive high exponent at `R = 1 − δ + η` for
every bin `δ ∈ ℝ`. -/
theorem zeroDensityTheta_balanced_barrier {n ℓ η : ℝ} (hn : 1 < n) (hη : -5 / 6 < η)
    (hθ : probeTheta n (1 - ℓ) ℓ < zeroDensityTheta n η) (δ : ℝ) :
    0 < endpointExponentOrder n ((1 - ℓ) / 2) ((1 - ℓ) / 2) ℓ
          (lowBoundaryGenOrder n ((1 - ℓ) / 2) ((1 - ℓ) / 2) ℓ) δ (δ / 2) (1 - δ + η) := by
  have hn0 : n ≠ 0 := by linarith
  have hsub : 0 < n - 1 := by linarith
  have hden : 0 < 5 + 6 * η := by linarith
  have hlow : lowBoundaryGenOrder n ((1 - ℓ) / 2) ((1 - ℓ) / 2) ℓ =
      1 - (1 + 3 * ℓ) / (2 * n) := by
    unfold lowBoundaryGenOrder
    rw [sub_self, max_self, show (1 - ℓ) / 2 + (1 - ℓ) / 2 + ℓ - 1 = 0 by ring, max_self]
    ring
  have hprobe : probeTheta n (1 - ℓ) ℓ = (n - 1 - 3 * ℓ) / (n - 1) := by
    unfold probeTheta
    rw [show 1 - ℓ + ℓ - 1 = 0 by ring, max_self]
    ring
  rw [hprobe] at hθ
  unfold zeroDensityTheta at hθ
  have hℓ : (1 - 2 * η) / (5 + 6 * η) < ℓ := by
    rw [div_lt_div_iff₀ hsub (mul_pos hden hsub)] at hθ
    have hmul : (n - 1 - 3 * ℓ) * (5 + 6 * η) < (5 + 6 * η) * n - 8 :=
      lt_of_mul_lt_mul_right (by linarith) hsub.le
    rw [div_lt_iff₀ hden]
    linarith
  rw [hlow, endpointExponentOrder_balanced_edge_spillover hn0]
  have hrew : (5 * ℓ - 1) / 4 + (1 + 3 * ℓ) / 2 * (1 - δ + η - (1 - δ)) =
      ((5 + 6 * η) * ℓ - (1 - 2 * η)) / 4 := by ring
  rw [hrew]
  rw [div_lt_iff₀ hden] at hℓ
  linarith

/-- **Near-floor continuum spillover.** Past `ℓ = 1/5` (`θ < (5n − 8)/(5(n − 1))` on the balanced
edge), pure zero-density `R = 1 − δ` leaves a strictly positive `(5ℓ − 1)/4` exponent on every bin
`δ`; nonpositivity requires `R ≤ (3 + ℓ)/(2(1 + 3ℓ)) − δ`. -/
theorem balanced_edge_nonpos_iff {n ℓ : ℝ} (hn0 : n ≠ 0) (hℓ : -1 / 3 < ℓ) (δ R : ℝ) :
    endpointExponentOrder n ((1 - ℓ) / 2) ((1 - ℓ) / 2) ℓ (1 - (1 + 3 * ℓ) / (2 * n))
        δ (δ / 2) R ≤ 0 ↔
      R ≤ (3 + ℓ) / (2 * (1 + 3 * ℓ)) - δ := by
  rw [endpointExponentOrder_balanced_edge_spillover hn0]
  have hpos : 0 < 1 + 3 * ℓ := by linarith
  constructor <;> intro h
  · rw [le_sub_iff_add_le, le_div_iff₀ (by linarith)]
    linarith
  · rw [le_sub_iff_add_le, le_div_iff₀ (by linarith)] at h
    linarith

/-- **Square-root signed cancellation reaches `(n − 2)/(n − 1)` uniformly across all bins.** At
`(1/3, 1/3, 1/3)` (`θ = (n − 2)/(n − 1)`, `σ₀ = 1 − 1/n`), `R = (1 − δ)/2` makes
`endpointExponentOrder ≤ 0` for every `δ ≤ 2/3` and `q ≤ δ/2` (covering `0 ≤ δ ≤ 2σ₀ − 1 = 1 − 2/n`
for every `2 ≤ n ≤ 6`). -/
theorem endpointExponentOrder_sqrt_cancellation_nonpos {n δ q : ℝ} (hn0 : n ≠ 0)
    (hδ : δ ≤ 2 / 3) (hq : q ≤ δ / 2) :
    endpointExponentOrder n (1 / 3) (1 / 3) (1 / 3) (1 - 1 / n) δ q ((1 - δ) / 2) ≤ 0 := by
  have heq : endpointExponentOrder n (1 / 3) (1 / 3) (1 / 3) (1 - 1 / n) δ q ((1 - δ) / 2) =
      (q - δ / 2) / 3 + (3 * δ - 2) / 6 := by
    unfold endpointExponentOrder
    field_simp
    ring
  rw [heq]
  linarith

/-! ### Global two-phase bifurcation under floor-bin signed Gram exponent `R₀` -/

/-- Symmetric-phase minimum twist exponent `((6 R₀ − 1)n − 8)/((6 R₀ − 1)(n − 1))`, governing
`R₀ ≥ ½ + 1/n` across all `(lx, ly, ℓ) ∈ ℝ³`. -/
def signedGramSymmetricTheta (n R₀ : ℝ) : ℝ :=
  ((6 * R₀ - 1) * n - 8) / ((6 * R₀ - 1) * (n - 1))

/-- Symmetry-broken minimum twist exponent on `0 ≤ lx`, `0 ≤ ly`, governing
`½ ≤ R₀ ≤ ½ + 1/n` for `n ≥ 3`. -/
def signedGramBrokenTheta (n R₀ : ℝ) : ℝ :=
  ((2 * n * R₀ + 1) * (n - 1) - 3 * (2 * n * (1 - R₀) + 1)) / ((2 * n * R₀ + 1) * (n - 1))

/-- Exact landmarks of `signedGramSymmetricTheta`: `R₀ = 1` gives the triangle-inequality floor,
`R₀ = 9/10` matches the tuple-saving low corner (`46/55` at `n = 6`, `σ₀ = 28/33`), `R₀ = 5/6`
reaches the universal reflection floor `(n − 2)/(n − 1)`, and `R₀ = ½ + 1/n` is the critical
bifurcation point `n / (n + 3)`. -/
theorem signedGramSymmetricTheta_landmarks {n : ℝ} (hn : 1 < n) :
    signedGramSymmetricTheta n 1 = (5 * n - 8) / (5 * (n - 1)) ∧
      signedGramSymmetricTheta n (9 / 10) = (11 * n - 20) / (11 * (n - 1)) ∧
      signedGramSymmetricTheta n (5 / 6) = (n - 2) / (n - 1) ∧
      signedGramSymmetricTheta n (1 / 2 + 1 / n) = n / (n + 3) := by
  have hn0 : n ≠ 0 := by linarith
  have hsub : n - 1 ≠ 0 := by linarith
  have hn3 : n + 3 ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold signedGramSymmetricTheta; field_simp; ring
  · unfold signedGramSymmetricTheta; field_simp; ring
  · unfold signedGramSymmetricTheta; field_simp; ring
  · unfold signedGramSymmetricTheta; field_simp; ring

/-- The symmetric and broken curves meet continuously at `R₀ = ½ + 1/n` and reconverge at
`R₀ = ½` to `(n − 4)/(n − 1)`. -/
theorem signedGram_phase_endpoints {n : ℝ} (hn : 1 < n) :
    signedGramBrokenTheta n (1 / 2 + 1 / n) = signedGramSymmetricTheta n (1 / 2 + 1 / n) ∧
      signedGramBrokenTheta n (1 / 2) = (n - 4) / (n - 1) ∧
      signedGramSymmetricTheta n (1 / 2) = (n - 4) / (n - 1) := by
  have hn0 : n ≠ 0 := by linarith
  have hsub : n - 1 ≠ 0 := by linarith
  have hn1 : n + 1 ≠ 0 := by linarith
  have hn3 : n + 3 ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold signedGramBrokenTheta signedGramSymmetricTheta; field_simp; ring
  · unfold signedGramBrokenTheta; field_simp; ring
  · unfold signedGramSymmetricTheta; field_simp; ring

/-- **Global symmetric-phase floor theorem.** For every order `n ≥ 2`, every floor-bin exponent
`R₀ ≥ ½ + 1/n`, and every `(lx, ly, ℓ) ∈ ℝ³` (in both Gram regimes),
`probeThetaGen n lx ly ℓ < signedGramSymmetricTheta n R₀` forces strictly positive floor-bin high
exponent at `R₀`. -/
theorem endpointExponentOrder_signedGram_pos_of_lt {n lx ly ℓ R₀ : ℝ}
    (hn : 2 ≤ n) (hR₀ : 1 / 2 + 1 / n ≤ R₀)
    (hθ : probeThetaGen n lx ly ℓ < signedGramSymmetricTheta n R₀) :
    0 < endpointExponentOrder n lx ly ℓ (lowBoundaryGenOrder n lx ly ℓ) 0 0 R₀ := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) < n := by linarith
  have hrpos : 0 < 1 / n := by positivity
  set c : ℝ := 6 * R₀ - 1
  have hcpos : 2 < c := by simp only [c]; linarith
  have hcne : c ≠ 0 := by linarith
  have hlow_target : positiveFormTheta n (1 - 4 / (c * n)) = signedGramSymmetricTheta n R₀ := by
    have hsub : n - 1 ≠ 0 := by linarith
    unfold positiveFormTheta signedGramSymmetricTheta
    simp only [c]
    field_simp
    ring
  have hσ : lowBoundaryGenOrder n lx ly ℓ < 1 - 4 / (c * n) := by
    have hmon := positiveFormBoundary_strictMono hn1 hθ
    rw [positiveFormBoundary_probeThetaGen hn0.ne' hn1.ne', ← hlow_target,
      positiveFormBoundary_positiveFormTheta hn0.ne' hn1.ne'] at hmon
    exact hmon
  set ν : ℝ := max 0 (ly - lx)
  set μ : ℝ := max 0 (lx + ly + ℓ - 1)
  have hν0 : 0 ≤ ν := le_max_left _ _
  have hν1 : ly - lx ≤ ν := le_max_right _ _
  have hμ0 : 0 ≤ μ := le_max_left _ _
  have hμ1 : lx + ly + ℓ - 1 ≤ μ := le_max_right _ _
  set A : ℝ := 1 - 4 / c - lx - ν / 2 + ℓ
  set B : ℝ := μ - (lx + ly + ℓ - 1)
  set C : ℝ := ν - (ly - lx)
  have hB : 0 ≤ B := sub_nonneg.mpr hμ1
  have hC : 0 ≤ C := sub_nonneg.mpr hν1
  have hσ_rew : 1 - 4 / (c * n) - lowBoundaryGenOrder n lx ly ℓ = A / n - μ / 2 := by
    unfold lowBoundaryGenOrder
    change 1 - 4 / (c * n) - (1 - (1 - lx - ν / 2 + ℓ) / n + μ / 2) = A / n - μ / 2
    simp only [A]
    field_simp
    ring
  have hAn : 0 < A / n - μ / 2 := by linarith
  have hApos : 0 < A := by
    have hAn0 : 0 < A / n := by linarith
    exact (div_pos_iff_of_pos_right hn0).mp hAn0
  have hR_coef : 0 ≤ R₀ - 1 / 6 - 5 / (3 * n) := by
    have hdiff : (1 / 2 + 1 / n) - (1 / 6 + 5 / (3 * n)) = (n - 2) / (3 * n) := by
      field_simp
      ring
    have hnn : 0 ≤ (n - 2) / (3 * n) := div_nonneg (by linarith) (by linarith)
    linarith
  have hE_rew : endpointExponentOrder n lx ly ℓ (lowBoundaryGenOrder n lx ly ℓ) 0 0 R₀ =
      (R₀ - 1 / 6 - 5 / (3 * n)) * A + 5 / 3 * (A / n - μ / 2) +
        1 / 3 * B + 1 / 6 * C + 1 / 2 * (R₀ - (1 / 2 + 1 / n)) * ν := by
    unfold endpointExponentOrder lowBoundaryGenOrder
    change (1 + 0) * (1 - ly) / 2 - (1 - (1 - lx - ν / 2 + ℓ) / n + μ / 2) - ℓ / 2 + 0 * ℓ +
        (1 - lx + ℓ) * (R₀ + 0 / 2 - 1 / n) =
      (R₀ - 1 / 6 - 5 / (3 * n)) * A + 5 / 3 * (A / n - μ / 2) +
        1 / 3 * B + 1 / 6 * C + 1 / 2 * (R₀ - (1 / 2 + 1 / n)) * ν
    simp only [A, B, C, c]
    field_simp
    ring
  rw [hE_rew]
  have ht1 : 0 ≤ (R₀ - 1 / 6 - 5 / (3 * n)) * A := mul_nonneg hR_coef hApos.le
  have ht2 : 0 ≤ 1 / 2 * (R₀ - (1 / 2 + 1 / n)) * ν :=
    mul_nonneg (by linarith) hν0
  linarith

/-- Attainment of `signedGramSymmetricTheta n R₀` at the balanced edge point
`((4 R₀ − 2)/(6 R₀ − 1), (4 R₀ − 2)/(6 R₀ − 1), (3 − 2 R₀)/(6 R₀ − 1))`. -/
theorem signedGramSymmetricTheta_attained {n R₀ : ℝ} (hn0 : n ≠ 0) (hn1 : n ≠ 1)
    (hR : 1 / 6 < R₀) :
    let c := 6 * R₀ - 1
    let x := (4 * R₀ - 2) / c
    let ℓ := (3 - 2 * R₀) / c
    probeThetaGen n x x ℓ = signedGramSymmetricTheta n R₀ ∧
      endpointExponentOrder n x x ℓ (lowBoundaryGenOrder n x x ℓ) 0 0 R₀ = 0 := by
  dsimp only
  set c : ℝ := 6 * R₀ - 1
  have hc : c ≠ 0 := by simp only [c]; linarith
  have hsub : n - 1 ≠ 0 := sub_ne_zero.mpr hn1
  have hsum : (4 * R₀ - 2) / c + (4 * R₀ - 2) / c + (3 - 2 * R₀) / c - 1 = 0 := by
    simp only [c]; field_simp; ring
  refine ⟨?_, ?_⟩
  · unfold probeThetaGen signedGramSymmetricTheta
    rw [sub_self, max_self, hsum, max_self]
    simp only [c]; field_simp; ring
  · unfold endpointExponentOrder lowBoundaryGenOrder
    rw [sub_self, max_self, hsum, max_self]
    simp only [c]; field_simp; ring

/-- **Global symmetry-broken floor theorem (`½ ≤ R₀ ≤ ½ + 1/n`).** For every order `n ≥ 3`,
`R₀ ∈ [½, ½ + 1/n]`, and physical scales `0 ≤ lx`, `0 ≤ ly`, `ℓ ∈ ℝ`,
`probeThetaGen n lx ly ℓ < signedGramBrokenTheta n R₀` forces strictly positive floor-bin high
exponent at `R₀`. -/
theorem endpointExponentOrder_signedGram_broken_pos_of_lt {n lx ly ℓ R₀ : ℝ}
    (hn : 3 ≤ n) (hR0 : 1 / 2 ≤ R₀) (hR1 : R₀ ≤ 1 / 2 + 1 / n)
    (hlx : 0 ≤ lx) (hly : 0 ≤ ly)
    (hθ : probeThetaGen n lx ly ℓ < signedGramBrokenTheta n R₀) :
    0 < endpointExponentOrder n lx ly ℓ (lowBoundaryGenOrder n lx ly ℓ) 0 0 R₀ := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) < n := by linarith
  set d : ℝ := 2 * n * R₀ + 1
  have hdpos : 0 < d := by simp only [d]; nlinarith
  have hdne : d ≠ 0 := hdpos.ne'
  set ℓs : ℝ := (2 * n * (1 - R₀) + 1) / d
  have hlow_target : positiveFormTheta n (1 - (1 + 3 * ℓs) / (2 * n)) =
      signedGramBrokenTheta n R₀ := by
    have hsub : n - 1 ≠ 0 := by linarith
    unfold positiveFormTheta signedGramBrokenTheta
    simp only [ℓs, d]
    field_simp
    ring
  have hσ : lowBoundaryGenOrder n lx ly ℓ < 1 - (1 + 3 * ℓs) / (2 * n) := by
    have hmon := positiveFormBoundary_strictMono hn1 hθ
    rw [positiveFormBoundary_probeThetaGen hn0.ne' hn1.ne', ← hlow_target,
      positiveFormBoundary_positiveFormTheta hn0.ne' hn1.ne'] at hmon
    exact hmon
  set ν : ℝ := max 0 (ly - lx)
  set μ : ℝ := max 0 (lx + ly + ℓ - 1)
  have hν1 : ly - lx ≤ ν := le_max_right _ _
  have hμ0 : 0 ≤ μ := le_max_left _ _
  have hμ1 : lx + ly + ℓ - 1 ≤ μ := le_max_right _ _
  set A' : ℝ := (1 - 3 * ℓs) / 2 - lx - ν / 2 + ℓ
  set B : ℝ := μ - (lx + ly + ℓ - 1)
  set C : ℝ := ν - (ly - lx)
  have hB : 0 ≤ B := sub_nonneg.mpr hμ1
  have hC : 0 ≤ C := sub_nonneg.mpr hν1
  have hσ_rew : 1 - (1 + 3 * ℓs) / (2 * n) - lowBoundaryGenOrder n lx ly ℓ = A' / n - μ / 2 := by
    unfold lowBoundaryGenOrder
    change 1 - (1 + 3 * ℓs) / (2 * n) - (1 - (1 - lx - ν / 2 + ℓ) / n + μ / 2) = A' / n - μ / 2
    simp only [A']
    field_simp
    ring
  have hAn : 0 < A' / n - μ / 2 := by linarith
  have hApos : 0 < A' := (div_pos_iff_of_pos_right hn0).mp (by linarith : 0 < A' / n)
  have hE_rew : endpointExponentOrder n lx ly ℓ (lowBoundaryGenOrder n lx ly ℓ) 0 0 R₀ =
      ((2 * R₀ * n * (n + 1) + n ^ 2 - 6 * n - 2) / (3 * n ^ 2)) * A' +
        (2 - 2 * R₀ / 3 + 2 / (3 * n)) * (A' / n - μ / 2) +
        (1 / 2 + 1 / n - R₀) * lx +
        1 / 3 * (3 / 2 + 1 / n - R₀) * B +
        1 / 3 * (R₀ - 1 / n) * C := by
    unfold endpointExponentOrder lowBoundaryGenOrder
    change (1 + 0) * (1 - ly) / 2 - (1 - (1 - lx - ν / 2 + ℓ) / n + μ / 2) - ℓ / 2 + 0 * ℓ +
        (1 - lx + ℓ) * (R₀ + 0 / 2 - 1 / n) =
      ((2 * R₀ * n * (n + 1) + n ^ 2 - 6 * n - 2) / (3 * n ^ 2)) * A' +
        (2 - 2 * R₀ / 3 + 2 / (3 * n)) * (A' / n - μ / 2) +
        (1 / 2 + 1 / n - R₀) * lx +
        1 / 3 * (3 / 2 + 1 / n - R₀) * B +
        1 / 3 * (R₀ - 1 / n) * C
    simp only [A', B, C, ℓs, d]
    field_simp
    ring
  rw [hE_rew]
  have h1n_le : 1 / n ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    linarith
  have hnum_pos : 0 < 2 * R₀ * n * (n + 1) + n ^ 2 - 6 * n - 2 := by
    have hmul : n * (n + 1) ≤ 2 * R₀ * n * (n + 1) := by
      have hnn : 0 ≤ n * (n + 1) := by positivity
      nlinarith
    have hquad : 0 < n * (n + 1) + n ^ 2 - 6 * n - 2 := by
      have hid : n * (n + 1) + n ^ 2 - 6 * n - 2 = 2 * (n - 3) ^ 2 + 7 * (n - 3) + 1 := by ring
      rw [hid]
      nlinarith [sq_nonneg (n - 3)]
    linarith
  have ht1 : 0 < ((2 * R₀ * n * (n + 1) + n ^ 2 - 6 * n - 2) / (3 * n ^ 2)) * A' :=
    mul_pos (div_pos hnum_pos (by positivity)) hApos
  have ht2 : 0 < (2 - 2 * R₀ / 3 + 2 / (3 * n)) * (A' / n - μ / 2) :=
    mul_pos (by linarith) hAn
  have ht3 : 0 ≤ (1 / 2 + 1 / n - R₀) * lx := mul_nonneg (by linarith) hlx
  have ht4 : 0 ≤ 1 / 3 * (3 / 2 + 1 / n - R₀) * B := mul_nonneg (by linarith) hB
  have ht5 : 0 ≤ 1 / 3 * (R₀ - 1 / n) * C := mul_nonneg (by linarith) hC
  linarith

/-- Attainment of `signedGramBrokenTheta n R₀` on the `lx = 0` boundary and strict improvement
over every balanced geometry throughout the open interval `R₀ ∈ (½, ½ + 1/n)`. -/
theorem signedGramBrokenTheta_attained_and_lt {n R₀ : ℝ} (hn : 2 ≤ n)
    (hR0 : 1 / 2 < R₀) (hR1 : R₀ < 1 / 2 + 1 / n) :
    let d := 2 * n * R₀ + 1
    let ly := 2 * (2 * R₀ - 1) * n / d
    let ℓ := (2 * n * (1 - R₀) + 1) / d
    0 < ly ∧
      probeThetaGen n 0 ly ℓ = signedGramBrokenTheta n R₀ ∧
      endpointExponentOrder n 0 ly ℓ (lowBoundaryGenOrder n 0 ly ℓ) 0 0 R₀ = 0 ∧
      signedGramBrokenTheta n R₀ < signedGramSymmetricTheta n R₀ := by
  dsimp only
  have hn0 : (0 : ℝ) < n := by linarith
  have hsub : 0 < n - 1 := by linarith
  set d : ℝ := 2 * n * R₀ + 1
  have hdpos : 0 < d := by simp only [d]; nlinarith
  have hdne : d ≠ 0 := hdpos.ne'
  set c : ℝ := 6 * R₀ - 1
  have hcpos : 0 < c := by simp only [c]; linarith
  have hcne : c ≠ 0 := hcpos.ne'
  have hly_pos : 0 < 2 * (2 * R₀ - 1) * n / d := div_pos (by nlinarith) hdpos
  have hsum : 0 + 2 * (2 * R₀ - 1) * n / d + (2 * n * (1 - R₀) + 1) / d - 1 = 0 := by
    simp only [d]; field_simp; ring
  refine ⟨hly_pos, ?_, ?_, ?_⟩
  · unfold probeThetaGen signedGramBrokenTheta
    rw [sub_zero, max_eq_right hly_pos.le, hsum, max_self]
    simp only [d]; field_simp; ring
  · unfold endpointExponentOrder lowBoundaryGenOrder
    rw [sub_zero, max_eq_right hly_pos.le, hsum, max_self]
    simp only [d]; field_simp; ring
  · have hdiff : signedGramSymmetricTheta n R₀ - signedGramBrokenTheta n R₀ =
        6 * (2 * R₀ - 1) * (n * (1 / 2 + 1 / n - R₀)) / (c * d * (n - 1)) := by
      unfold signedGramSymmetricTheta signedGramBrokenTheta
      simp only [c, d]
      field_simp
      ring
    have hpos_num : 0 < 6 * (2 * R₀ - 1) * (n * (1 / 2 + 1 / n - R₀)) :=
      mul_pos (by linarith) (mul_pos hn0 (by linarith))
    have hpos_diff : 0 < signedGramSymmetricTheta n R₀ - signedGramBrokenTheta n R₀ := by
      rw [hdiff]
      exact div_pos hpos_num (mul_pos (mul_pos hcpos hdpos) hsub)
    linarith

end

end GaloisForLFunctions.FamilyContinuationTheory.Budget
