import GaloisForLFunctions.HTGeometry.CofinalCholeskyFiniteFrame
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Clock capacity and the global Hilbert boundary

The finite inverse-Cholesky innovation packet becomes an orthonormal coordinate packet.  This
module supplies both missing Hilbert steps: the finite packet has its exact minimum-energy
representative, and an infinite packet has a unique normal representative exactly when its
innovation sequence lies in `ℓ²`.  Boundedness of all finite capacities is equivalent to the same
condition.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ENNReal NNReal lp

noncomputable section

theorem star_memℓp_two (eta : ℕ → ℂ) (heta : Memℓp eta 2) :
    Memℓp (fun n => star (eta n)) 2 := by
  apply memℓp_gen
  have hsum := heta.summable (by norm_num)
  simpa [norm_star] using hsum

/-- The finite normal representative of a prescribed packet in orthonormal clock coordinates. -/
def finiteHilbertBoundary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {N : ℕ} (phi : Fin N → E) (eta : Fin N → ℂ) : E :=
  ∑ i, star (eta i) • phi i

theorem inner_finiteHilbertBoundary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {N : ℕ} (phi : Fin N → E) (hphi : Orthonormal ℂ phi)
    (eta : Fin N → ℂ) (i : Fin N) :
    inner ℂ (phi i) (finiteHilbertBoundary phi eta) = star (eta i) := by
  exact hphi.inner_right_fintype (fun i => star (eta i)) i

theorem norm_sq_finiteHilbertBoundary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {N : ℕ} (phi : Fin N → E) (hphi : Orthonormal ℂ phi)
    (eta : Fin N → ℂ) :
    ‖finiteHilbertBoundary phi eta‖ ^ 2 = ∑ i, ‖eta i‖ ^ 2 := by
  have hinner := hphi.inner_sum (fun i => star (eta i))
    (fun i => star (eta i)) Finset.univ
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hre : ‖finiteHilbertBoundary phi eta‖ ^ 2 =
      (∑ i ∈ Finset.univ, star (star (eta i)) * star (eta i)).re := by
    have h := congrArg Complex.re hinner
    simpa [finiteHilbertBoundary, pow_two, Complex.mul_re] using h
  rw [hre]
  simp [RCLike.star_def, Complex.mul_conj, ← Complex.sq_norm,
    pow_two, Complex.mul_re]

/-- **Finite minimum-energy theorem.**  The finite representative in orthonormal clock
coordinates has squared norm `∑ ‖eta_i‖²`, and no vector with the same response packet has
smaller norm. -/
theorem finiteHilbertBoundary_isMinimum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {N : ℕ} (phi : Fin N → E) (hphi : Orthonormal ℂ phi)
    (eta : Fin N → ℂ) (y : E)
    (hy : ∀ i, inner ℂ (phi i) y = star (eta i)) :
    ‖finiteHilbertBoundary phi eta‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  rw [norm_sq_finiteHilbertBoundary phi hphi eta]
  have hbound := hphi.sum_inner_products_le y (s := Finset.univ)
  simpa [hy, norm_star] using hbound

/-- The Hilbert vector with prescribed square-summable coordinates in a Hilbert basis. -/
noncomputable def hilbertBoundaryOfSquareSummable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ℕ ℂ E) (eta : ℕ → ℂ) (heta : Memℓp eta 2) : E :=
  b.repr.symm
    (⟨fun n => star (eta n), star_memℓp_two eta heta⟩ : ℓ²(ℕ, ℂ))

theorem inner_hilbertBoundaryOfSquareSummable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ℕ ℂ E) (eta : ℕ → ℂ) (heta : Memℓp eta 2) (n : ℕ) :
    inner ℂ (b n) (hilbertBoundaryOfSquareSummable b eta heta) = star (eta n) := by
  rw [← b.repr_apply_apply]
  simp [hilbertBoundaryOfSquareSummable]

theorem norm_sq_hilbertBoundaryOfSquareSummable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ℕ ℂ E) (eta : ℕ → ℂ) (heta : Memℓp eta 2) :
    ‖hilbertBoundaryOfSquareSummable b eta heta‖ ^ 2 =
      ∑' n, ‖eta n‖ ^ 2 := by
  let a : ℓ²(ℕ, ℂ) :=
    ⟨fun n => star (eta n), star_memℓp_two eta heta⟩
  have hnorm := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) a
  change ‖b.repr.symm a‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map]
  simpa [a, Pi.star_apply, norm_star] using hnorm

theorem memℓp_two_of_hilbertBasis_coordinates
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ℕ ℂ E) (eta : ℕ → ℂ) (y : E)
    (hy : ∀ n, inner ℂ (b n) y = star (eta n)) :
    Memℓp eta 2 := by
  apply memℓp_gen
  have hs := b.orthonormal.inner_products_summable y
  simpa [hy, norm_star] using hs

theorem hilbertBasis_coordinates_unique
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ℕ ℂ E) (eta : ℕ → ℂ) (y z : E)
    (hy : ∀ n, inner ℂ (b n) y = star (eta n))
    (hz : ∀ n, inner ℂ (b n) z = star (eta n)) : y = z := by
  apply b.repr.injective
  ext n
  rw [b.repr_apply_apply, b.repr_apply_apply, hy n, hz n]

/-- **Riesz--Fischer clock-boundary classification.**  A complete prescribed coordinate packet
has a unique normal Hilbert representative exactly when it is square-summable. -/
theorem existsUnique_hilbertBasis_coordinates_iff_memℓp
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ℕ ℂ E) (eta : ℕ → ℂ) :
    (∃! y : E, ∀ n, inner ℂ (b n) y = star (eta n)) ↔ Memℓp eta 2 := by
  constructor
  · rintro ⟨y, hy, _⟩
    exact memℓp_two_of_hilbertBasis_coordinates b eta y hy
  · intro heta
    refine ⟨hilbertBoundaryOfSquareSummable b eta heta,
      inner_hilbertBoundaryOfSquareSummable b eta heta, ?_⟩
    intro y hy
    exact hilbertBasis_coordinates_unique b eta y
      (hilbertBoundaryOfSquareSummable b eta heta) hy
      (inner_hilbertBoundaryOfSquareSummable b eta heta)

theorem memℓp_two_iff_summable_norm_sq (eta : ℕ → ℂ) :
    Memℓp eta 2 ↔ Summable (fun n => ‖eta n‖ ^ 2) := by
  simpa using (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (f := eta) (by norm_num))

theorem summable_norm_sq_iff_bounded_partialCapacity (eta : ℕ → ℂ) :
    Summable (fun n => ‖eta n‖ ^ 2) ↔
      ∃ C : ℝ, ∀ N, ∑ n ∈ Finset.range (N + 1), ‖eta n‖ ^ 2 ≤ C := by
  constructor
  · intro hsum
    refine ⟨∑' n, ‖eta n‖ ^ 2, fun N => ?_⟩
    exact hsum.sum_le_tsum (Finset.range (N + 1)) fun n _ => sq_nonneg ‖eta n‖
  · rintro ⟨C, hC⟩
    have hCnonneg : 0 ≤ C :=
      (sq_nonneg ‖eta 0‖).trans (by simpa using hC 0)
    apply summable_of_sum_range_le (fun n => sq_nonneg ‖eta n‖)
    intro N
    cases N with
    | zero => simpa using hCnonneg
    | succ N => simpa [Finset.sum_range_succ] using hC N

/-- Normal Hilbert representability, square summability, and uniform boundedness of finite clock
capacity are equivalent. -/
theorem existsUnique_hilbertBasis_coordinates_iff_bounded_partialCapacity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ℕ ℂ E) (eta : ℕ → ℂ) :
    (∃! y : E, ∀ n, inner ℂ (b n) y = star (eta n)) ↔
      ∃ C : ℝ, ∀ N, ∑ n ∈ Finset.range (N + 1), ‖eta n‖ ^ 2 ≤ C := by
  rw [existsUnique_hilbertBasis_coordinates_iff_memℓp,
    memℓp_two_iff_summable_norm_sq,
    summable_norm_sq_iff_bounded_partialCapacity]

end

end GaloisForLFunctions.HTGeometry
