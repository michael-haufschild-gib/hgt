import GaloisForLFunctions.HTGeometry.ComplexSecondKind
import GaloisForLFunctions.HTGeometry.NevanlinnaClassicalInterface

/-!
# The Plücker relation behind `A D - B C = 1`

The determinant identity of the Nevanlinna matrix rests on a single algebraic fact about two pairs
of solutions of the recurrence, one evaluated at `0` and one at `z`.  Writing

`P = Qₙ(0), P' = Qₙ₊₁(0), S = Rₙ(0), S' = Rₙ₊₁(0)`,
`p = Qₙ(z), p' = Qₙ₊₁(z), r = Rₙ(z), r' = Rₙ₊₁(z)`,

each pair has the *same* constant Wronskian.  The four bilinear Christoffel--Darboux sums that make
up `A, B, C, D` then combine into

`(S' r - S r') (P' p - P p') + (p' S - p S') (P' r - P r') = 1`.

The mechanism is that the left side is identically `(p' r - p r') (S P' - S' P)` — a product of the
two Wronskians — with all eight mixed terms cancelling in pairs.  Stating it for an arbitrary
commutative ring isolates the combinatorics from the analysis.
-/

namespace HTGeometry

variable {R : Type*} [CommRing R]

/-- The two Wronskians factor out of the bilinear combination: all eight mixed terms cancel in
pairs, leaving a product. -/
theorem wronskian_bilinear_factor (P P' S S' p p' r r' : R) :
    (S' * r - S * r') * (P' * p - P * p') + (p' * S - p * S') * (P' * r - P * r')
      = (p' * r - p * r') * (S * P' - S' * P) := by
  ring

/-- **The Plücker relation.**  Two solution pairs with the same constant Wronskian `-1` satisfy the
bilinear identity that produces `A D - B C = 1`. -/
theorem wronskian_pluecker (P P' S S' p p' r r' : R)
    (h1 : P' * S - P * S' = -1) (h2 : p' * r - p * r' = -1) :
    (S' * r - S * r') * (P' * p - P * p') + (p' * S - p * S') * (P' * r - P * r') = 1 := by
  rw [wronskian_bilinear_factor, h2]
  linear_combination -h1

/-- The same relation for an arbitrary common Wronskian value `c`: the bilinear combination is
`c ^ 2`. -/
theorem wronskian_pluecker_sq (P P' S S' p p' r r' c : R)
    (h1 : P' * S - P * S' = c) (h2 : p' * r - p * r' = c) :
    (S' * r - S * r') * (P' * p - P * p') + (p' * S - p * S') * (P' * r - P * r') = c ^ 2 := by
  rw [wronskian_bilinear_factor, h2]
  linear_combination c * h1

/-! ## The determinant precursor

Substituting the four Christoffel--Darboux identities at `(0, z)` into the Plücker relation.  Both
Wronskian hypotheses are supplied by `monicOrthoC_wronskian` at `0` and at `z`, with the *same*
value `-(hₙ / h₀)`, so `wronskian_pluecker_sq` applies directly in the monic variables.

The result is the exact relation between the four bilinear sums that makes `A D - B C = 1`. -/

variable {s : ℕ → ℝ}

theorem nevanlinna_determinant_precursor (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z ^ 2 *
      ((∑ k ∈ Finset.range (n + 1), secondKindC s k 0 * secondKindC s k z /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) *
        (∑ k ∈ Finset.range (n + 1), monicOrthoC s k 0 * monicOrthoC s k z /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
      - (∑ k ∈ Finset.range (n + 1), monicOrthoC s k z * secondKindC s k 0 /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) *
        (∑ k ∈ Finset.range (n + 1), monicOrthoC s k 0 * secondKindC s k z /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)))
      = z * ((∑ k ∈ Finset.range (n + 1), monicOrthoC s k z * secondKindC s k 0 /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
        - (∑ k ∈ Finset.range (n + 1), monicOrthoC s k 0 * secondKindC s k z /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))) := by
  have h0 : ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s 0)
  have hn : ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h.self_ne_zero (monicOrtho_ne_zero s n)
  have hpl := wronskian_pluecker_sq
    (monicOrthoC s n 0) (monicOrthoC s (n + 1) 0)
    (secondKindC s n 0) (secondKindC s (n + 1) 0)
    (monicOrthoC s n z) (monicOrthoC s (n + 1) z)
    (secondKindC s n z) (secondKindC s (n + 1) z)
    (-((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) /
      ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ))
    (by
      have hw := monicOrthoC_wronskian h n 0
      rw [hw]
      push_cast
      ring)
    (by
      have hw := monicOrthoC_wronskian h n z
      rw [hw]
      push_cast
      ring)
  have F1 : secondKindC s (n + 1) 0 * secondKindC s n z -
      secondKindC s n 0 * secondKindC s (n + 1) z
      = ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
        ((0 - z) * ∑ k ∈ Finset.range (n + 1), secondKindC s k 0 * secondKindC s k z /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) := by
    rw [secondKindChristoffelDarbouxC h n 0 z]
    field_simp
  have F2 : monicOrthoC s (n + 1) 0 * monicOrthoC s n z -
      monicOrthoC s n 0 * monicOrthoC s (n + 1) z
      = ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
        ((0 - z) * ∑ k ∈ Finset.range (n + 1), monicOrthoC s k 0 * monicOrthoC s k z /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) := by
    rw [christoffelDarbouxC h n 0 z]
    field_simp
  have F3 : monicOrthoC s (n + 1) z * secondKindC s n 0 -
      monicOrthoC s n z * secondKindC s (n + 1) 0
      = ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
        ((z - 0) * (∑ k ∈ Finset.range (n + 1), monicOrthoC s k z * secondKindC s k 0 /
            ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
          - 1 / ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ)) := by
    rw [mixedChristoffelDarbouxC h n z 0]
    field_simp [h0, hn]
    try ring
  have F4 : monicOrthoC s (n + 1) 0 * secondKindC s n z -
      monicOrthoC s n 0 * secondKindC s (n + 1) z
      = ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
        ((0 - z) * (∑ k ∈ Finset.range (n + 1), monicOrthoC s k 0 * secondKindC s k z /
            ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
          - 1 / ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ)) := by
    rw [mixedChristoffelDarbouxC h n 0 z]
    field_simp [h0, hn]
    try ring
  rw [F1, F2, F3, F4] at hpl
  -- cancel the common factor `hₙ ^ 2`
  have hX : (0 - z) * (∑ k ∈ Finset.range (n + 1), secondKindC s k 0 * secondKindC s k z /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) *
      ((0 - z) * ∑ k ∈ Finset.range (n + 1), monicOrthoC s k 0 * monicOrthoC s k z /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
      + ((z - 0) * (∑ k ∈ Finset.range (n + 1), monicOrthoC s k z * secondKindC s k 0 /
            ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
          - 1 / ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ)) *
        ((0 - z) * (∑ k ∈ Finset.range (n + 1), monicOrthoC s k 0 * secondKindC s k z /
            ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
          - 1 / ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ))
      = (1 / ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ)) ^ 2 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hn) ?_
    linear_combination hpl
  field_simp at hX
  refine mul_left_cancel₀ h0 ?_
  linear_combination hX

/-! ## The truncated Nevanlinna matrix

The four entries built from the bilinear sums, scaled by `h₀` so that the determinant identity holds
for an arbitrary moment sequence rather than only a normalised one. -/

/-- `Aₙ(z) = h₀ z ∑ Rₖ(0) Rₖ(z) / hₖ`. -/
noncomputable def nevA (s : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
    ∑ k ∈ Finset.range (n + 1), secondKindC s k 0 * secondKindC s k z /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)

/-- `Bₙ(z) = -1 + h₀ z ∑ Qₖ(z) Rₖ(0) / hₖ`. -/
noncomputable def nevB (s : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  -1 + ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
    ∑ k ∈ Finset.range (n + 1), monicOrthoC s k z * secondKindC s k 0 /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)

/-- `Cₙ(z) = 1 + h₀ z ∑ Qₖ(0) Rₖ(z) / hₖ`. -/
noncomputable def nevC (s : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  1 + ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
    ∑ k ∈ Finset.range (n + 1), monicOrthoC s k 0 * secondKindC s k z /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)

/-- `Dₙ(z) = h₀ z ∑ Qₖ(0) Qₖ(z) / hₖ`. -/
noncomputable def nevD (s : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
    ∑ k ∈ Finset.range (n + 1), monicOrthoC s k 0 * monicOrthoC s k z /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)

/-- **The determinant identity `Aₙ Dₙ - Bₙ Cₙ = 1`.**  Exact at every truncation level `n`, for
every complex `z`, and for an arbitrary positive definite moment sequence. -/
theorem nevA_mul_nevD_sub_nevB_mul_nevC (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    nevA s n z * nevD s n z - nevB s n z * nevC s n z = 1 := by
  have hprec := nevanlinna_determinant_precursor h n z
  simp only [nevA, nevB, nevC, nevD]
  linear_combination ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * hprec

/-! ## Convergence of the Nevanlinna series

Bounded kernel roots make each of the four bilinear series absolutely summable, by Cauchy--Schwarz
on the partial sums.  This is what allows the truncated matrix to have a limit. -/

theorem sum_range_norm_weighted_le (h : PositiveMomentForm s) (n : ℕ) (f g : ℕ → ℂ) :
    ∑ k ∈ Finset.range (n + 1),
        ‖f k‖ * ‖g k‖ / momentInner s (monicOrtho s k) (monicOrtho s k)
      ≤ kernelRoot s f n * kernelRoot s g n := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hnn : 0 ≤ ∑ k ∈ Finset.range (n + 1),
      ‖f k‖ * ‖g k‖ / momentInner s (monicOrtho s k) (monicOrtho s k) :=
    Finset.sum_nonneg fun k _ =>
      div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hpos k).le
  have hA : 0 ≤ ∑ k ∈ Finset.range (n + 1),
      ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k) :=
    Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (hpos k).le
  rw [kernelRoot, kernelRoot, ← Real.sqrt_mul hA]
  have hsq := Real.sqrt_le_sqrt (weightedSum_sq_le h n f g)
  rwa [Real.sqrt_sq hnn] at hsq

/-- **Absolute summability of a bilinear moment series** from bounds on the two kernel roots. -/
theorem summable_weighted_of_bounds (h : PositiveMomentForm s) (f g : ℕ → ℂ) {Kf Kg : ℝ}
    (hf : ∀ N, kernelRoot s f N ≤ Kf) (hg : ∀ N, kernelRoot s g N ≤ Kg) :
    Summable (fun k => f k * g k /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hKf : 0 ≤ Kf := le_trans (kernelRoot_nonneg s f 0) (hf 0)
  have hKg : 0 ≤ Kg := le_trans (kernelRoot_nonneg s g 0) (hg 0)
  have hterm : ∀ k, ‖f k * g k /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)‖
      = ‖f k‖ * ‖g k‖ / momentInner s (monicOrtho s k) (monicOrtho s k) := by
    intro k
    rw [norm_div, norm_mul]
    congr 1
    simp [abs_of_pos (hpos k)]
  refine Summable.of_norm ?_
  refine summable_of_sum_range_le (c := Kf * Kg) (fun k => norm_nonneg _) ?_
  intro n
  match n with
  | 0 => simpa using mul_nonneg hKf hKg
  | (m + 1) =>
      have hrw : ∑ k ∈ Finset.range (m + 1),
          ‖f k * g k / ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)‖
          = ∑ k ∈ Finset.range (m + 1),
            ‖f k‖ * ‖g k‖ / momentInner s (monicOrtho s k) (monicOrtho s k) :=
        Finset.sum_congr rfl fun k _ => hterm k
      rw [hrw]
      refine le_trans (sum_range_norm_weighted_le h m f g) ?_
      exact mul_le_mul (hf m) (hg m) (kernelRoot_nonneg s g m) hKf

/-! ## The limiting Nevanlinna matrix

Passing `n → ∞`.  The determinant identity holds at every truncation, so it holds in the limit. -/

open Filter Topology

/-- Partial sums over `range (n+1)` converge to the `tsum`. -/
private theorem tendsto_partial_succ (f : ℕ → ℂ) (hf : Summable f) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), f k) atTop (nhds (∑' k, f k)) :=
  (hf.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

noncomputable def nevAinf (s : ℕ → ℝ) (z : ℂ) : ℂ :=
  ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
    ∑' k, secondKindC s k 0 * secondKindC s k z /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)

noncomputable def nevBinf (s : ℕ → ℝ) (z : ℂ) : ℂ :=
  -1 + ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
    ∑' k, monicOrthoC s k z * secondKindC s k 0 /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)

noncomputable def nevCinf (s : ℕ → ℝ) (z : ℂ) : ℂ :=
  1 + ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
    ∑' k, monicOrthoC s k 0 * secondKindC s k z /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)

noncomputable def nevDinf (s : ℕ → ℝ) (z : ℂ) : ℂ :=
  ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z *
    ∑' k, monicOrthoC s k 0 * monicOrthoC s k z /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)

/-- **The determinant identity in the limit.**  With both kernels bounded at `0` and at `z`, the
four series converge and `A D - B C = 1` for the limiting Nevanlinna matrix. -/
theorem nevAinf_mul_nevDinf_sub_nevBinf_mul_nevCinf (h : PositiveMomentForm s) (z : ℂ)
    (h0b : BoundedKernel s 0) (hzb : BoundedKernel s z) :
    nevAinf s z * nevDinf s z - nevBinf s z * nevCinf s z = 1 := by
  obtain ⟨S0, P0, _, _, hS0, hP0⟩ := h0b
  obtain ⟨Sz, Pz, _, _, hSz, hPz⟩ := hzb
  have sA := summable_weighted_of_bounds h (fun k => secondKindC s k 0)
    (fun k => secondKindC s k z) hP0 hPz
  have sB := summable_weighted_of_bounds h (fun k => monicOrthoC s k z)
    (fun k => secondKindC s k 0) hSz hP0
  have sC := summable_weighted_of_bounds h (fun k => monicOrthoC s k 0)
    (fun k => secondKindC s k z) hS0 hPz
  have sD := summable_weighted_of_bounds h (fun k => monicOrthoC s k 0)
    (fun k => monicOrthoC s k z) hS0 hSz
  have tA : Tendsto (fun n => nevA s n z) atTop (nhds (nevAinf s z)) := by
    simp only [nevA, nevAinf]
    exact (tendsto_partial_succ _ sA).const_mul _
  have tB : Tendsto (fun n => nevB s n z) atTop (nhds (nevBinf s z)) := by
    simp only [nevB, nevBinf]
    exact ((tendsto_partial_succ _ sB).const_mul _).const_add _
  have tC : Tendsto (fun n => nevC s n z) atTop (nhds (nevCinf s z)) := by
    simp only [nevC, nevCinf]
    exact ((tendsto_partial_succ _ sC).const_mul _).const_add _
  have tD : Tendsto (fun n => nevD s n z) atTop (nhds (nevDinf s z)) := by
    simp only [nevD, nevDinf]
    exact (tendsto_partial_succ _ sD).const_mul _
  have tcomb : Tendsto (fun n => nevA s n z * nevD s n z - nevB s n z * nevC s n z) atTop
      (nhds (nevAinf s z * nevDinf s z - nevBinf s z * nevCinf s z)) :=
    (tA.mul tD).sub (tB.mul tC)
  have hconst : (fun n => nevA s n z * nevD s n z - nevB s n z * nevC s n z) = fun _ => (1 : ℂ) := by
    funext n
    exact nevA_mul_nevD_sub_nevB_mul_nevC h n z
  rw [hconst] at tcomb
  exact tendsto_nhds_unique tcomb tendsto_const_nhds

/-! ## Cauchy--Schwarz over an arbitrary index set

The `range`-indexed bound of `ComplexSecondKind` suffices for the kernel roots, but the tail
estimates behind uniform convergence need an arbitrary `Finset` — in particular `Finset.Ico N M`. -/

theorem weightedSum_sq_le_finset (h : PositiveMomentForm s) (t : Finset ℕ) (f g : ℕ → ℂ) :
    (∑ j ∈ t, ‖f j‖ * ‖g j‖ / momentInner s (monicOrtho s j) (monicOrtho s j)) ^ 2
      ≤ (∑ j ∈ t, ‖f j‖ ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j)) *
        (∑ j ∈ t, ‖g j‖ ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j)) := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hmul : ∀ j, Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j)) *
      Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))
      = momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => Real.mul_self_sqrt (hpos j).le
  have hcs : (∑ j ∈ t,
        (‖f j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) *
          (‖g j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j)))) ^ 2
      ≤ (∑ j ∈ t, (‖f j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) ^ 2) *
        (∑ j ∈ t, (‖g j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have e1 : ∑ j ∈ t,
      (‖f j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) *
        (‖g j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j)))
      = ∑ j ∈ t, ‖f j‖ * ‖g j‖ / momentInner s (monicOrtho s j) (monicOrtho s j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_mul_div_comm, hmul j]
  have e2 : ∑ j ∈ t, (‖f j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) ^ 2
      = ∑ j ∈ t, ‖f j‖ ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, Real.sq_sqrt (hpos j).le]
  have e3 : ∑ j ∈ t, (‖g j‖ / Real.sqrt (momentInner s (monicOrtho s j) (monicOrtho s j))) ^ 2
      = ∑ j ∈ t, ‖g j‖ ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, Real.sq_sqrt (hpos j).le]
  rw [e1, e2, e3] at hcs
  exact hcs

/-- **Tail bound.**  Over any index set, a bilinear moment sum is bounded by the product of the two
root sums.  Applied to `Finset.Ico N M` this is the uniform Cauchy estimate. -/
theorem norm_sum_weighted_le_finset (h : PositiveMomentForm s) (t : Finset ℕ) (f g : ℕ → ℂ) :
    ‖∑ j ∈ t, f j * g j /
        ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)‖
      ≤ Real.sqrt (∑ j ∈ t, ‖f j‖ ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j)) *
        Real.sqrt (∑ j ∈ t, ‖g j‖ ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j)) := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hterm : ∀ j, ‖f j * g j /
      ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)‖
      = ‖f j‖ * ‖g j‖ / momentInner s (monicOrtho s j) (monicOrtho s j) := by
    intro j
    rw [norm_div, norm_mul]
    congr 1
    simp [abs_of_pos (hpos j)]
  have hstep1 : ‖∑ j ∈ t, f j * g j /
      ((momentInner s (monicOrtho s j) (monicOrtho s j) : ℝ) : ℂ)‖
      ≤ ∑ j ∈ t, ‖f j‖ * ‖g j‖ / momentInner s (monicOrtho s j) (monicOrtho s j) := by
    refine le_trans (norm_sum_le _ _) ?_
    exact le_of_eq (Finset.sum_congr rfl fun j _ => hterm j)
  have hnn : 0 ≤ ∑ j ∈ t, ‖f j‖ * ‖g j‖ /
      momentInner s (monicOrtho s j) (monicOrtho s j) :=
    Finset.sum_nonneg fun j _ =>
      div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hpos j).le
  have hA : 0 ≤ ∑ j ∈ t, ‖f j‖ ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j) :=
    Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hpos j).le
  refine le_trans hstep1 ?_
  rw [← Real.sqrt_mul hA]
  have hsq := Real.sqrt_le_sqrt (weightedSum_sq_le_finset h t f g)
  rwa [Real.sqrt_sq hnn] at hsq

/-! ## The uniform tail estimate

The half of the Cauchy criterion that is uniform in the point: one factor of the tail is controlled
by the kernel bound, which on a transfer disc is the *same constant* for every point of the disc. -/

theorem sqrt_sum_Ico_le (h : PositiveMomentForm s) (N M : ℕ) (g : ℕ → ℂ) {Kg : ℝ}
    (hg : ∀ n, kernelRoot s g n ≤ Kg) :
    Real.sqrt (∑ k ∈ Finset.Ico N M,
      ‖g k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)) ≤ Kg := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hKg : 0 ≤ Kg := le_trans (kernelRoot_nonneg s g 0) (hg 0)
  match M with
  | 0 => simpa using hKg
  | (m + 1) =>
      have hsub : Finset.Ico N (m + 1) ⊆ Finset.range (m + 1) := by
        intro x hx
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
      have hle : ∑ k ∈ Finset.Ico N (m + 1),
            ‖g k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)
          ≤ ∑ k ∈ Finset.range (m + 1),
            ‖g k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro j _ _
        exact div_nonneg (sq_nonneg _) (hpos j).le
      have hroot : ∑ k ∈ Finset.range (m + 1),
          ‖g k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)
          = kernelRoot s g m ^ 2 := (kernelRoot_sq h g m).symm
      rw [hroot] at hle
      have hstep := Real.sqrt_le_sqrt hle
      rw [Real.sqrt_sq (kernelRoot_nonneg s g m)] at hstep
      exact le_trans hstep (hg m)

/-- **The uniform tail estimate.**  A tail of a bilinear moment series is bounded by the square root
of the corresponding tail of the *first* series times a bound for the second kernel root.  On a
transfer disc the second factor is the same constant for every point, so only the first factor
varies — and it tends to zero. -/
theorem norm_sum_Ico_weighted_le (h : PositiveMomentForm s) (N M : ℕ) (f g : ℕ → ℂ) {Kg : ℝ}
    (hg : ∀ n, kernelRoot s g n ≤ Kg) :
    ‖∑ k ∈ Finset.Ico N M, f k * g k /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)‖
      ≤ Real.sqrt (∑ k ∈ Finset.Ico N M,
          ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)) * Kg := by
  refine le_trans (norm_sum_weighted_le_finset h (Finset.Ico N M) f g) ?_
  refine mul_le_mul_of_nonneg_left (sqrt_sum_Ico_le h N M g hg) (Real.sqrt_nonneg _)

/-! ## The full uniform Cauchy criterion

Combining the uniform tail estimate with the fact that the tail of a convergent series vanishes.
The resulting bound depends on neither the upper index `M` nor the point of the disc. -/

theorem sum_Ico_le_tsum_sub_range (h : PositiveMomentForm s) (f : ℕ → ℂ)
    (hf : Summable (fun k => ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)))
    (N M : ℕ) :
    ∑ k ∈ Finset.Ico N M, ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)
      ≤ (∑' k, ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k))
        - ∑ k ∈ Finset.range N, ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k) := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hnn : ∀ j, 0 ≤ ‖f j‖ ^ 2 / momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => div_nonneg (sq_nonneg _) (hpos j).le
  rcases Nat.lt_or_ge M N with hMN | hNM
  · have hempty : Finset.Ico N M = ∅ := Finset.Ico_eq_empty_of_le hMN.le
    rw [hempty, Finset.sum_empty]
    have hNle : ∑ k ∈ Finset.range N,
        ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)
        ≤ ∑' k, ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k) :=
      hf.sum_le_tsum _ (fun i _ => hnn i)
    linarith
  · have hsplit : (∑ k ∈ Finset.Ico 0 N,
          ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k))
        + ∑ k ∈ Finset.Ico N M, ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)
        = ∑ k ∈ Finset.Ico 0 M, ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k) :=
      Finset.sum_Ico_consecutive _ (Nat.zero_le N) hNM
    rw [← Finset.range_eq_Ico, ← Finset.range_eq_Ico] at hsplit
    have hMle : ∑ k ∈ Finset.range M,
        ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)
        ≤ ∑' k, ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k) :=
      hf.sum_le_tsum _ (fun i _ => hnn i)
    linarith [hsplit, hMle]

/-- **Uniform Cauchy bound.**  The tail of the bilinear series is bounded by a quantity depending
only on `N` — not on the upper index `M`, and not on the point through which `g` is taken, beyond
the single constant `Kg`. -/
theorem norm_sum_Ico_weighted_le_tail (h : PositiveMomentForm s) (f g : ℕ → ℂ) {Kg : ℝ}
    (hg : ∀ n, kernelRoot s g n ≤ Kg)
    (hf : Summable (fun k => ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)))
    (N M : ℕ) :
    ‖∑ k ∈ Finset.Ico N M, f k * g k /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)‖
      ≤ Real.sqrt ((∑' k, ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k))
          - ∑ k ∈ Finset.range N, ‖f k‖ ^ 2 /
            momentInner s (monicOrtho s k) (monicOrtho s k)) * Kg := by
  have hKg : 0 ≤ Kg := le_trans (kernelRoot_nonneg s g 0) (hg 0)
  refine le_trans (norm_sum_Ico_weighted_le h N M f g hg) ?_
  refine mul_le_mul_of_nonneg_right ?_ hKg
  exact Real.sqrt_le_sqrt (sum_Ico_le_tsum_sub_range h f hf N M)

/-- The uniform Cauchy bound tends to zero. -/
theorem tendsto_uniformCauchyBound_zero (f : ℕ → ℂ) {Kg : ℝ}
    (hf : Summable (fun k => ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k))) :
    Tendsto (fun N => Real.sqrt
        ((∑' k, ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k))
          - ∑ k ∈ Finset.range N, ‖f k‖ ^ 2 /
            momentInner s (monicOrtho s k) (monicOrtho s k)) * Kg) atTop (nhds 0) := by
  have hpart := hf.hasSum.tendsto_sum_nat
  have htail : Tendsto (fun N =>
      (∑' k, ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k))
        - ∑ k ∈ Finset.range N, ‖f k‖ ^ 2 /
          momentInner s (monicOrtho s k) (monicOrtho s k)) atTop (nhds 0) := by
    have := tendsto_const_nhds (x :=
      ∑' k, ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)) (f := atTop (α := ℕ))
    simpa using this.sub hpart
  have hsqrt : Tendsto (fun N => Real.sqrt
      ((∑' k, ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k))
        - ∑ k ∈ Finset.range N, ‖f k‖ ^ 2 /
          momentInner s (monicOrtho s k) (monicOrtho s k))) atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp htail
    simpa using this
  simpa using hsqrt.mul_const Kg

/-- **Uniform Cauchy convergence.**  One threshold `N₀` works simultaneously for every upper index
`M` and every second family `g` obeying the kernel bound `Kg`.  On a transfer disc
`kernelRoot_bounds_propagate` supplies that single `Kg` for all points at once, so this is uniform
convergence of the bilinear series over the whole disc. -/
theorem uniformCauchy_weighted (h : PositiveMomentForm s) (f : ℕ → ℂ)
    (hf : Summable (fun k => ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)))
    (Kg : ℝ) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, ∀ g : ℕ → ℂ, (∀ n, kernelRoot s g n ≤ Kg) →
      ‖∑ k ∈ Finset.Ico N M, f k * g k /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)‖ < ε := by
  intro ε hε
  have htend := tendsto_uniformCauchyBound_zero (s := s) f (Kg := Kg) hf
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp htend ε hε
  refine ⟨N₀, fun N hN M g hg => ?_⟩
  have hbound := norm_sum_Ico_weighted_le_tail h f g hg hf N M
  have hlt := hN₀ N hN
  rw [Real.dist_eq, sub_zero] at hlt
  refine lt_of_le_of_lt hbound ?_
  exact lt_of_abs_lt hlt

/-! ## Bridge into mathlib's uniform-convergence API

Repackaging `uniformCauchy_weighted` as `UniformCauchySeqOn` for the partial sums, on any set of
points whose second kernel root obeys a common bound.  On a transfer disc that hypothesis is
`kernelRoot_bounds_propagate`. -/

/-- The partial sums of a bilinear moment series, as functions of the point. -/
noncomputable def bilinearPartialSum (s : ℕ → ℝ) (f : ℕ → ℂ) (G : ℂ → ℕ → ℂ)
    (N : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N, f k * G z k /
    ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)

theorem uniformCauchySeqOn_bilinearPartialSum (h : PositiveMomentForm s) (f : ℕ → ℂ)
    (hf : Summable (fun k => ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)))
    (Kg : ℝ) (G : ℂ → ℕ → ℂ) (U : Set ℂ)
    (hG : ∀ z ∈ U, ∀ n, kernelRoot s (G z) n ≤ Kg) :
    UniformCauchySeqOn (bilinearPartialSum s f G) atTop U := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := uniformCauchy_weighted h f hf Kg ε hε
  refine ⟨N₀, fun m hm n hn z hz => ?_⟩
  have hsub : ∀ a b : ℕ, a ≤ b →
      bilinearPartialSum s f G b z - bilinearPartialSum s f G a z
        = ∑ k ∈ Finset.Ico a b, f k * G z k /
          ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
    intro a b hab
    rw [bilinearPartialSum, bilinearPartialSum]
    exact (Finset.sum_Ico_eq_sub _ hab).symm
  rcases le_total n m with hnm | hmn
  · rw [Complex.dist_eq, hsub n m hnm]
    exact hN₀ n hn m (G z) (hG z hz)
  · rw [Complex.dist_eq, ← neg_sub, norm_neg, hsub m n hmn]
    exact hN₀ m hm n (G z) (hG z hz)

/-! ## Analyticity of the limit

A uniform limit of holomorphic functions is holomorphic.  The partial sums are polynomials in the
point whenever the family `G` is, so the limiting bilinear series is differentiable on any open set
carrying a common kernel-root bound. -/

theorem summable_normSq_of_kernelRoot_le (h : PositiveMomentForm s) (f : ℕ → ℂ) {Kf : ℝ}
    (hf : ∀ n, kernelRoot s f n ≤ Kf) :
    Summable (fun k => ‖f k‖ ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k)) := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hKf : 0 ≤ Kf := le_trans (kernelRoot_nonneg s f 0) (hf 0)
  refine summable_of_sum_range_le (c := Kf ^ 2)
    (fun k => div_nonneg (sq_nonneg _) (hpos k).le) ?_
  intro n
  match n with
  | 0 => simpa using sq_nonneg Kf
  | (m + 1) =>
      rw [← kernelRoot_sq h]
      have hnn := kernelRoot_nonneg s f m
      nlinarith [hf m, hnn, hKf]

/-- **Holomorphy of the limiting bilinear series.** -/
theorem differentiableOn_bilinearLimit (h : PositiveMomentForm s) (f : ℕ → ℂ) {Kf Kg : ℝ}
    (hf : ∀ n, kernelRoot s f n ≤ Kf)
    (G : ℂ → ℕ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hG : ∀ z ∈ U, ∀ n, kernelRoot s (G z) n ≤ Kg)
    (hdiff : ∀ N, DifferentiableOn ℂ (bilinearPartialSum s f G N) U) :
    DifferentiableOn ℂ (fun z => ∑' k, f k * G z k /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) U := by
  have hfs := summable_normSq_of_kernelRoot_le h f hf
  have hcauchy := uniformCauchySeqOn_bilinearPartialSum h f hfs Kg G U hG
  have hptw : ∀ z ∈ U, Tendsto (fun N => bilinearPartialSum s f G N z) atTop
      (nhds (∑' k, f k * G z k /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))) := by
    intro z hz
    exact (summable_weighted_of_bounds h f (G z) hf (hG z hz)).hasSum.tendsto_sum_nat
  have huniform := hcauchy.tendstoUniformlyOn_of_tendsto hptw
  have hloc : TendstoLocallyUniformlyOn (bilinearPartialSum s f G)
      (fun z => ∑' k, f k * G z k /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) atTop U :=
    huniform.tendstoLocallyUniformlyOn
  exact hloc.differentiableOn (Filter.Eventually.of_forall hdiff) hU

/-! ## Applying holomorphy to the Nevanlinna entries

The families are polynomial in the point, so the partial sums are differentiable and the previous
theorem applies. -/

theorem differentiable_monicOrthoC (s : ℕ → ℝ) (k : ℕ) :
    Differentiable ℂ (fun z : ℂ => monicOrthoC s k z) := by
  have hrw : (fun z : ℂ => monicOrthoC s k z)
      = fun z : ℂ => Polynomial.eval z ((monicOrtho s k).map (algebraMap ℝ ℂ)) := by
    funext z
    rw [monicOrthoC, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  rw [hrw]
  exact Polynomial.differentiable _

theorem differentiable_secondKindC (s : ℕ → ℝ) (k : ℕ) :
    Differentiable ℂ (fun z : ℂ => secondKindC s k z) := by
  have hrw : (fun z : ℂ => secondKindC s k z)
      = fun z : ℂ => Polynomial.eval z ((secondKind s k).map (algebraMap ℝ ℂ)) := by
    funext z
    rw [secondKindC, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  rw [hrw]
  exact Polynomial.differentiable _

theorem differentiableOn_bilinearPartialSum (s : ℕ → ℝ) (f : ℕ → ℂ) (G : ℂ → ℕ → ℂ)
    (hG : ∀ k, Differentiable ℂ (fun z => G z k)) (N : ℕ) (U : Set ℂ) :
    DifferentiableOn ℂ (bilinearPartialSum s f G N) U := by
  refine Differentiable.differentiableOn ?_
  have hterm : ∀ k ∈ Finset.range N,
      Differentiable ℂ (fun z : ℂ => f k * G z k /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) := by
    intro k _
    exact ((hG k).const_mul (f k)).div_const _
  unfold bilinearPartialSum
  have hEq : (fun z : ℂ => ∑ k ∈ Finset.range N, f k * G z k /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
      = ∑ k ∈ Finset.range N, (fun z : ℂ => f k * G z k /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) := by
    funext z
    simp
  rw [hEq]
  exact Differentiable.sum hterm

/-- **The `D` entry's series is holomorphic** on any open set with a uniform kernel bound. -/
theorem differentiableOn_nevD_series (h : PositiveMomentForm s) (U : Set ℂ) (hU : IsOpen U)
    {S0 Sz : ℝ}
    (hS0 : ∀ n, kernelRoot s (fun j => monicOrthoC s j 0) n ≤ S0)
    (hUz : ∀ z ∈ U, ∀ n, kernelRoot s (fun j => monicOrthoC s j z) n ≤ Sz) :
    DifferentiableOn ℂ (fun z => ∑' k, monicOrthoC s k 0 * monicOrthoC s k z /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) U :=
  differentiableOn_bilinearLimit h (fun k => monicOrthoC s k 0) hS0
    (fun z k => monicOrthoC s k z) U hU hUz
    (fun N => differentiableOn_bilinearPartialSum s _ _
      (fun k => differentiable_monicOrthoC s k) N U)

/-- **The `C` entry's series is holomorphic** on any open set with a uniform second-kind bound. -/
theorem differentiableOn_nevC_series (h : PositiveMomentForm s) (U : Set ℂ) (hU : IsOpen U)
    {S0 Pz : ℝ}
    (hS0 : ∀ n, kernelRoot s (fun j => monicOrthoC s j 0) n ≤ S0)
    (hUz : ∀ z ∈ U, ∀ n, kernelRoot s (fun j => secondKindC s j z) n ≤ Pz) :
    DifferentiableOn ℂ (fun z => ∑' k, monicOrthoC s k 0 * secondKindC s k z /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) U :=
  differentiableOn_bilinearLimit h (fun k => monicOrthoC s k 0) hS0
    (fun z k => secondKindC s k z) U hU hUz
    (fun N => differentiableOn_bilinearPartialSum s _ _
      (fun k => differentiable_secondKindC s k) N U)

/-- **The `A` entry's series is holomorphic.** -/
theorem differentiableOn_nevA_series (h : PositiveMomentForm s) (U : Set ℂ) (hU : IsOpen U)
    {P0 Pz : ℝ}
    (hP0 : ∀ n, kernelRoot s (fun j => secondKindC s j 0) n ≤ P0)
    (hUz : ∀ z ∈ U, ∀ n, kernelRoot s (fun j => secondKindC s j z) n ≤ Pz) :
    DifferentiableOn ℂ (fun z => ∑' k, secondKindC s k 0 * secondKindC s k z /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) U :=
  differentiableOn_bilinearLimit h (fun k => secondKindC s k 0) hP0
    (fun z k => secondKindC s k z) U hU hUz
    (fun N => differentiableOn_bilinearPartialSum s _ _
      (fun k => differentiable_secondKindC s k) N U)

/-- **The `B` entry's series is holomorphic.**  Its summand has the point-dependent factor first, so
the product is commuted before applying the general theorem. -/
theorem differentiableOn_nevB_series (h : PositiveMomentForm s) (U : Set ℂ) (hU : IsOpen U)
    {P0 Sz : ℝ}
    (hP0 : ∀ n, kernelRoot s (fun j => secondKindC s j 0) n ≤ P0)
    (hUz : ∀ z ∈ U, ∀ n, kernelRoot s (fun j => monicOrthoC s j z) n ≤ Sz) :
    DifferentiableOn ℂ (fun z => ∑' k, monicOrthoC s k z * secondKindC s k 0 /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)) U := by
  have hEq : (fun z : ℂ => ∑' k, monicOrthoC s k z * secondKindC s k 0 /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ))
      = fun z : ℂ => ∑' k, secondKindC s k 0 * monicOrthoC s k z /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ) := by
    funext z
    exact tsum_congr fun k => by ring
  rw [hEq]
  exact differentiableOn_bilinearLimit h (fun k => secondKindC s k 0) hP0
    (fun z k => monicOrthoC s k z) U hU hUz
    (fun N => differentiableOn_bilinearPartialSum s _ _
      (fun k => differentiable_monicOrthoC s k) N U)

/-! ## Capstone: the limiting Nevanlinna matrix is holomorphic and unimodular -/

/-- **The four limiting entries are holomorphic on any open set with uniform kernel bounds, and
satisfy `A D - B C = 1` there.**  This is the analytic content of the Nevanlinna matrix, modulo the
growth statement. -/
theorem nevanlinna_holomorphic_unimodular (h : PositiveMomentForm s) (U : Set ℂ) (hU : IsOpen U)
    {S0 P0 Sz Pz : ℝ}
    (hS0 : ∀ n, kernelRoot s (fun j => monicOrthoC s j 0) n ≤ S0)
    (hP0 : ∀ n, kernelRoot s (fun j => secondKindC s j 0) n ≤ P0)
    (hUS : ∀ z ∈ U, ∀ n, kernelRoot s (fun j => monicOrthoC s j z) n ≤ Sz)
    (hUP : ∀ z ∈ U, ∀ n, kernelRoot s (fun j => secondKindC s j z) n ≤ Pz)
    (h0b : BoundedKernel s 0) (hUb : ∀ z ∈ U, BoundedKernel s z) :
    DifferentiableOn ℂ (nevAinf s) U ∧ DifferentiableOn ℂ (nevBinf s) U ∧
      DifferentiableOn ℂ (nevCinf s) U ∧ DifferentiableOn ℂ (nevDinf s) U ∧
      ∀ z ∈ U, nevAinf s z * nevDinf s z - nevBinf s z * nevCinf s z = 1 := by
  have hlin : Differentiable ℂ (fun z : ℂ =>
      ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) * z) :=
    differentiable_id.const_mul _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold nevAinf
    exact hlin.differentiableOn.mul (differentiableOn_nevA_series h U hU hP0 hUP)
  · unfold nevBinf
    exact (hlin.differentiableOn.mul (differentiableOn_nevB_series h U hU hP0 hUS)).const_add _
  · unfold nevCinf
    exact (hlin.differentiableOn.mul (differentiableOn_nevC_series h U hU hS0 hUP)).const_add _
  · unfold nevDinf
    exact hlin.differentiableOn.mul (differentiableOn_nevD_series h U hU hS0 hUS)
  · intro z hz
    exact nevAinf_mul_nevDinf_sub_nevBinf_mul_nevCinf h z h0b (hUb z hz)

/-! ## Size bounds for the entries

The first step toward a growth statement: each entry is bounded by `h₀ |z|` times a product of
kernel roots.  Any exponential-type claim must control the kernel roots themselves, and this
isolates that as the only remaining unknown. -/

theorem norm_tsum_weighted_le (h : PositiveMomentForm s) (f g : ℕ → ℂ) {Kf Kg : ℝ}
    (hf : ∀ n, kernelRoot s f n ≤ Kf) (hg : ∀ n, kernelRoot s g n ≤ Kg) :
    ‖∑' k, f k * g k /
        ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)‖ ≤ Kf * Kg := by
  have hpos : ∀ j, 0 < momentInner s (monicOrtho s j) (monicOrtho s j) :=
    fun j => monicOrtho_inner_self_pos h j
  have hKf : 0 ≤ Kf := le_trans (kernelRoot_nonneg s f 0) (hf 0)
  have hKg : 0 ≤ Kg := le_trans (kernelRoot_nonneg s g 0) (hg 0)
  have hsum := summable_weighted_of_bounds h f g hf hg
  have hterm : ∀ k, ‖f k * g k /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)‖
      = ‖f k‖ * ‖g k‖ / momentInner s (monicOrtho s k) (monicOrtho s k) := by
    intro k
    rw [norm_div, norm_mul]
    congr 1
    simp [abs_of_pos (hpos k)]
  refine le_trans (norm_tsum_le_tsum_norm (by simpa [hterm] using hsum.norm)) ?_
  have hrw : ∑' k, ‖f k * g k /
      ((momentInner s (monicOrtho s k) (monicOrtho s k) : ℝ) : ℂ)‖
      = ∑' k, ‖f k‖ * ‖g k‖ / momentInner s (monicOrtho s k) (monicOrtho s k) :=
    tsum_congr hterm
  rw [hrw]
  have hs : Summable (fun k => ‖f k‖ * ‖g k‖ /
      momentInner s (monicOrtho s k) (monicOrtho s k)) := hsum.norm.congr hterm
  refine le_of_tendsto hs.hasSum.tendsto_sum_nat (Filter.Eventually.of_forall fun n => ?_)
  match n with
  | 0 => simpa using mul_nonneg hKf hKg
  | (m + 1) =>
      refine le_trans (sum_range_norm_weighted_le h m f g) ?_
      exact mul_le_mul (hf m) (hg m) (kernelRoot_nonneg s g m) hKf

/-- **Size bound for the `A` entry.** -/
theorem norm_nevAinf_le (h : PositiveMomentForm s) (z : ℂ) {P0 Pz : ℝ}
    (hP0 : ∀ n, kernelRoot s (fun j => secondKindC s j 0) n ≤ P0)
    (hPz : ∀ n, kernelRoot s (fun j => secondKindC s j z) n ≤ Pz) :
    ‖nevAinf s z‖
      ≤ momentInner s (monicOrtho s 0) (monicOrtho s 0) * ‖z‖ * (P0 * Pz) := by
  have h0pos : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  have hnormAux : ∀ c : ℝ, 0 < c → ‖(c : ℂ)‖ = c := by
    intro c hc
    simp [abs_of_pos hc]
  unfold nevAinf
  rw [norm_mul, norm_mul, hnormAux _ h0pos]
  refine mul_le_mul_of_nonneg_left (norm_tsum_weighted_le h _ _ hP0 hPz) ?_
  exact mul_nonneg h0pos.le (norm_nonneg _)

/-- **Size bound for the `D` entry.** -/
theorem norm_nevDinf_le (h : PositiveMomentForm s) (z : ℂ) {S0 Sz : ℝ}
    (hS0 : ∀ n, kernelRoot s (fun j => monicOrthoC s j 0) n ≤ S0)
    (hSz : ∀ n, kernelRoot s (fun j => monicOrthoC s j z) n ≤ Sz) :
    ‖nevDinf s z‖
      ≤ momentInner s (monicOrtho s 0) (monicOrtho s 0) * ‖z‖ * (S0 * Sz) := by
  have h0pos : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    monicOrtho_inner_self_pos h 0
  have hnormAux : ∀ c : ℝ, 0 < c → ‖(c : ℂ)‖ = c := by
    intro c hc
    simp [abs_of_pos hc]
  unfold nevDinf
  rw [norm_mul, norm_mul, hnormAux _ h0pos]
  refine mul_le_mul_of_nonneg_left (norm_tsum_weighted_le h _ _ hS0 hSz) ?_
  exact mul_nonneg h0pos.le (norm_nonneg _)

/-! ## The real-variable Nevanlinna matrix

The packaged interface `ClassicalNevanlinnaMatrixData ℝ` wants four *real* functions on the carrier
line with determinant one.  All three Christoffel--Darboux identities exist over `ℝ`, and
`wronskian_pluecker_sq` is stated for an arbitrary commutative ring, so the whole derivation
transfers verbatim. -/

theorem nevanlinna_determinant_precursor_real (h : PositiveMomentForm s) (n : ℕ) (x : ℝ) :
    momentInner s (monicOrtho s 0) (monicOrtho s 0) * x ^ 2 *
      ((∑ k ∈ Finset.range (n + 1), (secondKind s k).eval 0 * (secondKind s k).eval x /
          momentInner s (monicOrtho s k) (monicOrtho s k)) *
        (∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval 0 * (monicOrtho s k).eval x /
          momentInner s (monicOrtho s k) (monicOrtho s k))
      - (∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval x * (secondKind s k).eval 0 /
          momentInner s (monicOrtho s k) (monicOrtho s k)) *
        (∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval 0 * (secondKind s k).eval x /
          momentInner s (monicOrtho s k) (monicOrtho s k)))
      = x * ((∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval x * (secondKind s k).eval 0 /
          momentInner s (monicOrtho s k) (monicOrtho s k))
        - (∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval 0 * (secondKind s k).eval x /
          momentInner s (monicOrtho s k) (monicOrtho s k))) := by
  have h0 : momentInner s (monicOrtho s 0) (monicOrtho s 0) ≠ 0 :=
    h.self_ne_zero (monicOrtho_ne_zero s 0)
  have hn : momentInner s (monicOrtho s n) (monicOrtho s n) ≠ 0 :=
    h.self_ne_zero (monicOrtho_ne_zero s n)
  have hW : ∀ y : ℝ, (monicOrtho s (n + 1)).eval y * (secondKind s n).eval y
      - (monicOrtho s n).eval y * (secondKind s (n + 1)).eval y
      = -(momentInner s (monicOrtho s n) (monicOrtho s n) /
          momentInner s (monicOrtho s 0) (monicOrtho s 0)) := by
    intro y
    have hev := congrArg (Polynomial.eval y) (momentWronskian_eq h n)
    simpa [momentWronskian] using hev
  have hpl := wronskian_pluecker_sq
    ((monicOrtho s n).eval 0) ((monicOrtho s (n + 1)).eval 0)
    ((secondKind s n).eval 0) ((secondKind s (n + 1)).eval 0)
    ((monicOrtho s n).eval x) ((monicOrtho s (n + 1)).eval x)
    ((secondKind s n).eval x) ((secondKind s (n + 1)).eval x)
    (-(momentInner s (monicOrtho s n) (monicOrtho s n) /
      momentInner s (monicOrtho s 0) (monicOrtho s 0))) (hW 0) (hW x)
  have F1 : (secondKind s (n + 1)).eval 0 * (secondKind s n).eval x -
      (secondKind s n).eval 0 * (secondKind s (n + 1)).eval x
      = momentInner s (monicOrtho s n) (monicOrtho s n) *
        ((0 - x) * ∑ k ∈ Finset.range (n + 1), (secondKind s k).eval 0 * (secondKind s k).eval x /
          momentInner s (monicOrtho s k) (monicOrtho s k)) := by
    rw [secondKindChristoffelDarboux h n 0 x]
    field_simp
  have F2 : (monicOrtho s (n + 1)).eval 0 * (monicOrtho s n).eval x -
      (monicOrtho s n).eval 0 * (monicOrtho s (n + 1)).eval x
      = momentInner s (monicOrtho s n) (monicOrtho s n) *
        ((0 - x) * ∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval 0 * (monicOrtho s k).eval x /
          momentInner s (monicOrtho s k) (monicOrtho s k)) := by
    rw [christoffelDarboux h n 0 x]
    field_simp
  have F3 : (monicOrtho s (n + 1)).eval x * (secondKind s n).eval 0 -
      (monicOrtho s n).eval x * (secondKind s (n + 1)).eval 0
      = momentInner s (monicOrtho s n) (monicOrtho s n) *
        ((x - 0) * (∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval x * (secondKind s k).eval 0 /
            momentInner s (monicOrtho s k) (monicOrtho s k))
          - 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0)) := by
    rw [mixedChristoffelDarboux h n x 0]
    field_simp [h0, hn]
    try ring
  have F4 : (monicOrtho s (n + 1)).eval 0 * (secondKind s n).eval x -
      (monicOrtho s n).eval 0 * (secondKind s (n + 1)).eval x
      = momentInner s (monicOrtho s n) (monicOrtho s n) *
        ((0 - x) * (∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval 0 * (secondKind s k).eval x /
            momentInner s (monicOrtho s k) (monicOrtho s k))
          - 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0)) := by
    rw [mixedChristoffelDarboux h n 0 x]
    field_simp [h0, hn]
    try ring
  rw [F1, F2, F3, F4] at hpl
  have hX : (0 - x) * (∑ k ∈ Finset.range (n + 1), (secondKind s k).eval 0 *
        (secondKind s k).eval x / momentInner s (monicOrtho s k) (monicOrtho s k)) *
      ((0 - x) * ∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval 0 * (monicOrtho s k).eval x /
        momentInner s (monicOrtho s k) (monicOrtho s k))
      + ((x - 0) * (∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval x *
            (secondKind s k).eval 0 / momentInner s (monicOrtho s k) (monicOrtho s k))
          - 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0)) *
        ((0 - x) * (∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval 0 *
            (secondKind s k).eval x / momentInner s (monicOrtho s k) (monicOrtho s k))
          - 1 / momentInner s (monicOrtho s 0) (monicOrtho s 0))
      = (1 / momentInner s (monicOrtho s 0) (monicOrtho s 0)) ^ 2 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hn) ?_
    linear_combination hpl
  field_simp at hX
  refine mul_left_cancel₀ h0 ?_
  linear_combination hX

/-- Real-variable `A` entry at truncation level `n`. -/
noncomputable def nevAreal (s : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  momentInner s (monicOrtho s 0) (monicOrtho s 0) * x *
    ∑ k ∈ Finset.range (n + 1), (secondKind s k).eval 0 * (secondKind s k).eval x /
      momentInner s (monicOrtho s k) (monicOrtho s k)

/-- Real-variable `B` entry at truncation level `n`. -/
noncomputable def nevBreal (s : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  -1 + momentInner s (monicOrtho s 0) (monicOrtho s 0) * x *
    ∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval x * (secondKind s k).eval 0 /
      momentInner s (monicOrtho s k) (monicOrtho s k)

/-- Real-variable `C` entry at truncation level `n`. -/
noncomputable def nevCreal (s : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  1 + momentInner s (monicOrtho s 0) (monicOrtho s 0) * x *
    ∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval 0 * (secondKind s k).eval x /
      momentInner s (monicOrtho s k) (monicOrtho s k)

/-- Real-variable `D` entry at truncation level `n`. -/
noncomputable def nevDreal (s : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  momentInner s (monicOrtho s 0) (monicOrtho s 0) * x *
    ∑ k ∈ Finset.range (n + 1), (monicOrtho s k).eval 0 * (monicOrtho s k).eval x /
      momentInner s (monicOrtho s k) (monicOrtho s k)

/-- **The real determinant identity.**  Exactly the `det_one` field required by
`ClassicalNevanlinnaMatrixData ℝ`. -/
theorem nevAreal_mul_nevDreal_sub_nevBreal_mul_nevCreal (h : PositiveMomentForm s) (n : ℕ)
    (x : ℝ) :
    nevAreal s n x * nevDreal s n x - nevBreal s n x * nevCreal s n x = 1 := by
  have hprec := nevanlinna_determinant_precursor_real h n x
  simp only [nevAreal, nevBreal, nevCreal, nevDreal]
  linear_combination momentInner s (monicOrtho s 0) (monicOrtho s 0) * hprec

/-- **The truncated real Nevanlinna matrix data.**  A genuine inhabitant of the packaged interface
`ClassicalNevanlinnaMatrixData ℝ`, built from the moment sequence with no assumptions beyond
positive definiteness. -/
noncomputable def nevMatrixData (h : PositiveMomentForm s) (n : ℕ) :
    GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData ℝ where
  A := nevAreal s n
  B := nevBreal s n
  C := nevCreal s n
  D := nevDreal s n
  det_one := fun x => nevAreal_mul_nevDreal_sub_nevBreal_mul_nevCreal h n x

/-! ## Continuity of the real entries

The next fields of `ClassicalNevanlinnaExtremalFamily` after the matrix itself: continuity of the
denominator row `B`, `D`.  Each entry is a finite sum of polynomial evaluations against constants,
so all four are continuous. -/

theorem continuous_nevAreal (s : ℕ → ℝ) (n : ℕ) : Continuous (nevAreal s n) := by
  unfold nevAreal
  refine (continuous_const.mul continuous_id).mul ?_
  refine continuous_finsetSum _ fun k _ => ?_
  exact ((Polynomial.continuous _).const_mul _).div_const _

theorem continuous_nevBreal (s : ℕ → ℝ) (n : ℕ) : Continuous (nevBreal s n) := by
  unfold nevBreal
  refine Continuous.const_add ?_ _
  refine (continuous_const.mul continuous_id).mul ?_
  refine continuous_finsetSum _ fun k _ => ?_
  exact ((Polynomial.continuous _).mul_const _).div_const _

theorem continuous_nevCreal (s : ℕ → ℝ) (n : ℕ) : Continuous (nevCreal s n) := by
  unfold nevCreal
  refine Continuous.const_add ?_ _
  refine (continuous_const.mul continuous_id).mul ?_
  refine continuous_finsetSum _ fun k _ => ?_
  exact ((Polynomial.continuous _).const_mul _).div_const _

theorem continuous_nevDreal (s : ℕ → ℝ) (n : ℕ) : Continuous (nevDreal s n) := by
  unfold nevDreal
  refine (continuous_const.mul continuous_id).mul ?_
  refine continuous_finsetSum _ fun k _ => ?_
  exact ((Polynomial.continuous _).const_mul _).div_const _

/-- The denominator row of `nevMatrixData` is continuous: the two continuity fields of
`ClassicalNevanlinnaExtremalFamily` are discharged for the truncated matrix. -/
theorem continuous_nevMatrixData_B (h : PositiveMomentForm s) (n : ℕ) :
    Continuous (nevMatrixData h n).B :=
  continuous_nevBreal s n

theorem continuous_nevMatrixData_D (h : PositiveMomentForm s) (n : ℕ) :
    Continuous (nevMatrixData h n).D :=
  continuous_nevDreal s n

end HTGeometry
