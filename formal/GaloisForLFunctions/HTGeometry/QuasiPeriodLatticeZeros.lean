import GaloisForLFunctions.HTGeometry.QuasiPeriodEntireGrowth

/-!
# A zero of a quasi-periodic function drags a whole lattice box of zeros

If a quasi-periodic function vanishes at `z₀`, it vanishes on the entire coset `z₀ + Λ`, because
each lattice step only multiplies the value by a nonzero constant.  The coordinate box of size `N`
inside that coset contains `(2N+1)²` distinct points — distinct because `ℝ`-independent steps are
`ℤ`-independent — and all of them lie within distance `‖z₀ − c‖ + N(‖w₁‖ + ‖w₂‖)` of any centre `c`.

* `latticeBox` — the coordinate box of the coset, as a `Finset ℂ`;
* `card_latticeBox` — it has `(2N+1)²` elements;
* `norm_sub_le_of_mem_latticeBox` — it sits in a ball of radius linear in `N`;
* **`eq_zero_of_mem_latticeBox`** — a quasi-periodic function vanishes on all of it.

Together with `exists_exp_growth_bound_of_quasiperiods` this is the pair of estimates that Jensen's
inequality contradicts: quadratically many zeros in a disc of radius `r`, against a zero count that
is linear in `r` for a function of exponential type.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- The coordinate box of size `N` in the lattice coset `z₀ + ℤw₁ + ℤw₂`. -/
noncomputable def latticeBox (z₀ w₁ w₂ : ℂ) (N : ℕ) : Finset ℂ :=
  ((Finset.Icc (-(N : ℤ)) (N : ℤ)) ×ˢ (Finset.Icc (-(N : ℤ)) (N : ℤ))).image
    (fun p : ℤ × ℤ => z₀ + p.1 • w₁ + p.2 • w₂)

/-- `ℝ`-independent steps are `ℤ`-independent, so distinct integer coordinates give distinct lattice
points. -/
theorem latticeBox_injOn {w₁ w₂ : ℂ} (hindep : LinearIndependent ℝ ![w₁, w₂]) (z₀ : ℂ) :
    Function.Injective (fun p : ℤ × ℤ => z₀ + p.1 • w₁ + p.2 • w₂) := by
  have hZ : LinearIndependent ℤ ![w₁, w₂] := hindep.restrict_scalars' ℤ
  rintro ⟨m, n⟩ ⟨m', n'⟩ hp
  have hzero : (m - m') • w₁ + (n - n') • w₂ = 0 := by
    have : m • w₁ + n • w₂ = m' • w₁ + n' • w₂ := by
      have h := hp
      simp only at h
      linear_combination h
    simp only [sub_smul]
    rw [show (m • w₁ - m' • w₁) + (n • w₂ - n' • w₂)
      = (m • w₁ + n • w₂) - (m' • w₁ + n' • w₂) by ring, this, sub_self]
  have hcomb : ∑ i : Fin 2, ![m - m', n - n'] i • ![w₁, w₂] i = 0 := by
    rw [Fin.sum_univ_two]
    simpa using hzero
  have hcoeff := (Fintype.linearIndependent_iff.mp hZ) ![m - m', n - n'] hcomb
  have h0 := hcoeff 0
  have h1 := hcoeff 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hm : m = m' := by omega
  have hn : n = n' := by omega
  simp [hm, hn]

/-- The coordinate box has `(2N+1)²` elements. -/
theorem card_latticeBox {w₁ w₂ : ℂ} (hindep : LinearIndependent ℝ ![w₁, w₂]) (z₀ : ℂ) (N : ℕ) :
    (latticeBox z₀ w₁ w₂ N).card = (2 * N + 1) ^ (2 : ℕ) := by
  rw [latticeBox, Finset.card_image_of_injective _ (latticeBox_injOn hindep z₀),
    Finset.card_product, Int.card_Icc]
  have h : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [h, sq]

/-- Every point of the coordinate box lies within a distance linear in `N` of any centre. -/
theorem norm_sub_le_of_mem_latticeBox {z₀ w₁ w₂ : ℂ} {N : ℕ} {c u : ℂ}
    (hu : u ∈ latticeBox z₀ w₁ w₂ N) :
    ‖u - c‖ ≤ ‖z₀ - c‖ + N * (‖w₁‖ + ‖w₂‖) := by
  obtain ⟨⟨m, n⟩, hmem, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨hm, hn⟩ := Finset.mem_product.mp hmem
  rw [Finset.mem_Icc] at hm hn
  have hmn : |(m : ℝ)| ≤ (N : ℝ) := by
    rw [abs_le]
    constructor <;> exact_mod_cast by omega
  have hnn : |(n : ℝ)| ≤ (N : ℝ) := by
    rw [abs_le]
    constructor <;> exact_mod_cast by omega
  have hnorm₁ : ‖(m : ℤ) • w₁‖ = |(m : ℝ)| * ‖w₁‖ := by
    rw [zsmul_eq_mul, norm_mul]
    simp
  have hnorm₂ : ‖(n : ℤ) • w₂‖ = |(n : ℝ)| * ‖w₂‖ := by
    rw [zsmul_eq_mul, norm_mul]
    simp
  calc ‖z₀ + (m : ℤ) • w₁ + (n : ℤ) • w₂ - c‖
      = ‖(z₀ - c) + ((m : ℤ) • w₁ + (n : ℤ) • w₂)‖ := by ring_nf
    _ ≤ ‖z₀ - c‖ + ‖(m : ℤ) • w₁ + (n : ℤ) • w₂‖ := norm_add_le _ _
    _ ≤ ‖z₀ - c‖ + (‖(m : ℤ) • w₁‖ + ‖(n : ℤ) • w₂‖) := by
        gcongr
        exact norm_add_le _ _
    _ = ‖z₀ - c‖ + (|(m : ℝ)| * ‖w₁‖ + |(n : ℝ)| * ‖w₂‖) := by rw [hnorm₁, hnorm₂]
    _ ≤ ‖z₀ - c‖ + ((N : ℝ) * ‖w₁‖ + (N : ℝ) * ‖w₂‖) := by
        have hb₁ : |(m : ℝ)| * ‖w₁‖ ≤ (N : ℝ) * ‖w₁‖ :=
          mul_le_mul_of_nonneg_right hmn (norm_nonneg _)
        have hb₂ : |(n : ℝ)| * ‖w₂‖ ≤ (N : ℝ) * ‖w₂‖ :=
          mul_le_mul_of_nonneg_right hnn (norm_nonneg _)
        linarith
    _ = ‖z₀ - c‖ + N * (‖w₁‖ + ‖w₂‖) := by ring

/-- **A single zero produces a whole lattice box of zeros.** -/
theorem eq_zero_of_mem_latticeBox {f : ℂ → ℂ} {w₁ w₂ a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z)
    {z₀ : ℂ} (hz₀ : f z₀ = 0) (N : ℕ) {u : ℂ} (hu : u ∈ latticeBox z₀ w₁ w₂ N) : f u = 0 := by
  obtain ⟨⟨m, n⟩, _, rfl⟩ := Finset.mem_image.mp hu
  rw [quasiPeriodic_lattice ha hb h₁ h₂ m n z₀, hz₀, mul_zero]

end GaloisForLFunctions.HTGeometry
