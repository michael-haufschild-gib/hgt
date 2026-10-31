import GaloisForLFunctions.AdelicKreinGeometry.WeilsArchimedeanStateCountsTheZeros
import GaloisForLFunctions.AdelicKreinGeometry.TheGluingSquareIsSharp
import GaloisForLFunctions.HeckeKreinToeplitz.HeatCollisionsCountTheIndex

/-!
# The renormalized Hodge index

On the scaling surface the intersection matrix of the scaling correspondences `Γ_u`, `u ∈ ℚ_{>0}`,
is Weil's correlation `K(u⁻¹v)`. The pole class is the boost functional `ℓ(w) = Σ w_i u_i^{−1/2}`;
together with the successor class it spans a hyperbolic plane, and the archimedean place glues the
global state by the hyperplane `ℓ = 0` (`AdelicKreinGeometry.TheArchimedeanGluingFormula`).

A dilation datum `K` satisfies the **renormalized Hodge index** if it has no negative square on the
pole-orthogonal hyperplane: `κ^{(½)}(K) = 0`.

* **Hodge index = index one** (`renormalizedHodgeIndex_iff_negIndex_archGlue_eq_one`): `K` satisfies
  the renormalized Hodge index iff the glued state `K(|a|) − c|a|^{−1/2}|b|` has exactly one
  negative square, the successor's.
* **Hyperplane positivity** (`renormalizedHodgeIndex_iff`): equivalently every Gram form of `K` is
  nonnegative on the coefficient vectors of boost mass zero.
* **The pole class carries no zero** (`boostPolarIndex_ratCorr`): for Weil's correlation the
  hyperplane index is the whole index, `κ^{(½)}(K_ζ) = κ(K_ζ) = #` right zeros.
* **RH is the renormalized Hodge index** (`riemannHypothesis_iff_renormalizedHodgeIndex`,
  `riemannHypothesis_iff_hyperplane_nonneg`).
* **Pole blindness** (`renormalizedHodgeIndex_add_polePair_iff`): adding the pole pair at any
  strength changes nothing on the hyperplane.
* **Quantum bound** (`boostPolarIndex_ratCorr_le_iSup_collisionCharge`): the hyperplane index is
  bounded by the supremum of the horizontal collision charges of the heat flow; finitely many
  squares leave at least two heat collisions each at every small time
  (`eventually_two_mul_boostPolarIndex_le_collisionMassAfter`), infinitely many make the collision
  mass unbounded (`tendsto_collisionMassAfter_of_boostPolarIndex_eq_top`).

So inside the renormalized intersection theory RH is one statement: the pairing of scaling
correspondences is positive on the hyperplane orthogonal to the pole class.
-/

open Complex
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
  GaloisForLFunctions.AdelicKreinGeometry GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- The **renormalized Hodge index** of a dilation datum: no negative square on the
pole-orthogonal (boost-mass-zero) hyperplane. -/
def RenormalizedHodgeIndex (K : posUnits → ℂ) : Prop := boostPolarIndex K = 0

/-- **Hodge index = index one.** -/
theorem renormalizedHodgeIndex_iff_negIndex_archGlue_eq_one {K : posUnits → ℂ}
    (hK : IsHermKernel K) {c : ℝ} (hc : 0 < c) :
    RenormalizedHodgeIndex K ↔ negIndex (archGlue K c) = 1 := by
  rw [RenormalizedHodgeIndex, negIndex_archGlue_eq hK hc]
  constructor
  · intro h; rw [h, zero_add]
  · intro h
    have h' : boostPolarIndex K + 1 = 0 + 1 := by rw [h, zero_add]
    exact WithTop.add_right_cancel ENat.one_ne_top h'

theorem hermQuad_smul_vec {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (t : ℂ) (c : ι → ℂ) :
    hermQuad H (t • c) = Complex.normSq t * hermQuad H c := by
  simp only [hermQuad, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  rw [← mul_assoc, show t * star t = ((Complex.normSq t : ℝ) : ℂ) by
    rw [Complex.star_def, Complex.mul_conj], Complex.re_ofReal_mul]

/-- A Hermitian form has no negative square on `V` iff it is nonnegative on `V`. -/
theorem negIndexOn_eq_zero_iff {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
    (V : Submodule ℂ (ι → ℂ)) : negIndexOn H V = 0 ↔ ∀ c ∈ V, 0 ≤ hermQuad H c := by
  constructor
  · intro h c hc
    by_contra hneg
    push Not at hneg
    have hc0 : c ≠ 0 := fun h0 => by simp [h0, hermQuad] at hneg
    have hW : IsPosDefOn (-H) (Submodule.span ℂ {c}) := by
      intro x hx hx0
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
      have ht : t ≠ 0 := fun ht => hx0 (by simp [ht])
      rw [hermQuad_smul_vec, hermQuad_neg]
      have : 0 < Complex.normSq t := Complex.normSq_pos.mpr ht
      nlinarith
    have hle := finrank_le_negIndexOn ((Submodule.span_singleton_le_iff_mem c V).mpr hc) hW
    rw [finrank_span_singleton hc0, h] at hle
    exact absurd hle (by norm_num)
  · intro h
    obtain ⟨W, hWV, hdim, hW⟩ := exists_negIndexOn H V
    by_contra hne
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.mp (by rw [hdim]; exact Nat.one_le_iff_ne_zero.mpr hne))
    have := hW x hxW hx0
    rw [hermQuad_neg] at this
    linarith [h x (hWV hxW)]

/-- **Hyperplane positivity.** -/
theorem renormalizedHodgeIndex_iff (K : posUnits → ℂ) :
    RenormalizedHodgeIndex K ↔ ∀ (n : ℕ) (u : Fin n → posUnits) (w : Fin n → ℂ),
      boostMassU u w = 0 → 0 ≤ hermQuad (gram K u) w := by
  rw [RenormalizedHodgeIndex, boostPolarIndex, ENat.iSup_eq_zero]
  refine forall_congr' fun n => ?_
  rw [ENat.iSup_eq_zero]
  refine forall_congr' fun u => ?_
  rw [Nat.cast_eq_zero, negIndexOn_eq_zero_iff]
  exact forall_congr' fun w => by rw [LinearMap.mem_ker]

/-- **The pole class carries no zero**: on Weil's correlation the hyperplane index is the index. -/
theorem boostPolarIndex_ratCorr : boostPolarIndex ratCorr = negIndex zetaKernel := by
  have h1 := negIndex_weilArchState_eq (c := 1) one_pos
  rw [negIndex_weilArchState_eq_add_one one_pos] at h1
  exact (WithTop.add_right_cancel ENat.one_ne_top h1).symm

/-- **RH is the renormalized Hodge index of Weil's correlation.** -/
theorem riemannHypothesis_iff_renormalizedHodgeIndex :
    RiemannHypothesis ↔ RenormalizedHodgeIndex ratCorr := by
  rw [RenormalizedHodgeIndex, boostPolarIndex_ratCorr,
    riemannHypothesis_iff_negIndex_zetaKernel_eq_zero]

/-- **RH is positivity on the pole-orthogonal hyperplane.** -/
theorem riemannHypothesis_iff_hyperplane_nonneg :
    RiemannHypothesis ↔ ∀ (n : ℕ) (u : Fin n → posUnits) (w : Fin n → ℂ),
      boostMassU u w = 0 → 0 ≤ hermQuad (gram ratCorr u) w := by
  rw [riemannHypothesis_iff_renormalizedHodgeIndex, renormalizedHodgeIndex_iff]

/-- **Pole blindness**: the renormalized Hodge index does not see the pole pair. -/
theorem renormalizedHodgeIndex_add_polePair_iff (K : posUnits → ℂ) (t : ℝ) :
    RenormalizedHodgeIndex (fun u => K u + t * polePair u) ↔ RenormalizedHodgeIndex K := by
  rw [RenormalizedHodgeIndex, RenormalizedHodgeIndex, boostPolarIndex_add_polePair]

/-- **Quantum bound**: the hyperplane index of Weil's correlation is at most the largest horizontal
collision charge of the heat flow. -/
theorem boostPolarIndex_ratCorr_le_iSup_collisionCharge :
    boostPolarIndex ratCorr ≤ ⨆ T : ℝ, (RHTower.xiHorizontalCollisionCharge T : ℕ∞) := by
  rw [boostPolarIndex_ratCorr]
  exact negIndex_zetaKernel_le_iSup_horizontalCollisionCharge

/-- **The collision mass reads the hyperplane index**: with finitely many negative squares on the
pole-orthogonal hyperplane, every small heat time leaves at least two collisions per square. -/
theorem eventually_two_mul_boostPolarIndex_le_collisionMassAfter
    (h : boostPolarIndex ratCorr < ⊤) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      2 * boostPolarIndex ratCorr ≤ (_root_.RHTower.DeBruijn.collisionMassAfter t : ℕ∞) := by
  rw [boostPolarIndex_ratCorr] at h ⊢
  exact two_mul_negIndex_zetaKernel_le_collisionMassAfter h

/-- Infinitely many squares on the hyperplane make the collision mass unbounded as the heat
vanishes. -/
theorem tendsto_collisionMassAfter_of_boostPolarIndex_eq_top (h : boostPolarIndex ratCorr = ⊤) :
    Filter.Tendsto _root_.RHTower.DeBruijn.collisionMassAfter (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
  rw [boostPolarIndex_ratCorr] at h
  exact tendsto_collisionMassAfter_of_negIndex_eq_top h

end GaloisForLFunctions.RenormalizedIntersectionTheory
