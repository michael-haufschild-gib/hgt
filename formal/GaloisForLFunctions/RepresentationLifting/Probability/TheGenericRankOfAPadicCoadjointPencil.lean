import GaloisForLFunctions.RepresentationLifting.Probability.AlgebraicRelationsOfPadicCoordinates
import GaloisForLFunctions.HTGeometry.HankelSquareCatalecticant
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# A maximal minor on an integral p-adic slice

Maktouf's coadjoint slice argument chooses a single maximal minor for the
stabilizer equations. Over an integral box one such minor detects maximal
rank off a Haar-null hypersurface. This holds for polynomial matrices and
therefore for the affine matrices of bracket pairings on any integral slice.
-/

namespace GaloisForLFunctions.RepresentationLifting
open MeasureTheory
open scoped Classical
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {n a b : ℕ}

/-- Evaluate a polynomial matrix and transport its coefficients to a field. -/
def polynomialFieldMatrix {R K : Type*} [CommRing R] [Field K] (f : R →+* K)
    (P : Matrix (Fin a) (Fin b) (MvPolynomial (Fin n) R)) (x : Fin n → R) : Matrix (Fin a) (Fin b) K :=
  (P.map (MvPolynomial.eval x)).map f

/-- Rank of an integral matrix is read over the p-adic fraction field. -/
abbrev padicFieldMatrix (P : Matrix (Fin a) (Fin b) (MvPolynomial (Fin n) ℤ_[p]))
    (x : Fin n → ℤ_[p]) : Matrix (Fin a) (Fin b) ℚ_[p] :=
  polynomialFieldMatrix (PadicInt.Coe.ringHom (p:=p)) P x

private theorem fieldMinor_zero_iff {R K : Type*} [CommRing R] [Field K] (f : R →+* K)
    (hf : Function.Injective f) (P : Matrix (Fin a) (Fin b) (MvPolynomial (Fin n) R))
    (x : Fin n → R) {r : ℕ} (i : Fin r → Fin a) (j : Fin r → Fin b) :
    ((polynomialFieldMatrix f P x).submatrix i j).det=0 ↔
      MvPolynomial.eval x (P.submatrix i j).det=0 := by
  have he : ((polynomialFieldMatrix f P x).submatrix i j).det = f (MvPolynomial.eval x (P.submatrix i j).det) :=
    ((f.comp (MvPolynomial.eval x)).map_det (P.submatrix i j)).symm
  rw [he]
  exact ⟨fun h => hf (h.trans (map_zero f).symm),fun h => by rw [h,map_zero]⟩

private theorem maximal_rank_point {X K : Type*} [Nonempty X] [Field K]
    (F : X → Matrix (Fin a) (Fin b) K) : ∃ x, ∀ y, (F y).rank≤(F x).rank := by
  let S := (Finset.range (b+1)).filter (fun r => ∃ x, (F x).rank=r)
  have mem (x : X) : (F x).rank∈S :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (F x).rank_le_width),x,rfl⟩
  have hs : S.Nonempty := ⟨_,mem (Classical.arbitrary X)⟩
  obtain ⟨x,hx⟩ := (Finset.mem_filter.mp (S.max'_mem hs)).2
  exact ⟨x,fun y => (S.le_max' _ (mem y)).trans_eq hx.symm⟩

private theorem maximal_minor {K : Type*} [Field K] (M : Matrix (Fin a) (Fin b) K) :
    ∃ (i : Fin M.rank → Fin a) (j : Fin M.rank → Fin b), (M.submatrix i j).det≠0 := by
  generalize he : M.rank=r
  cases r with
  | zero =>
      exact ⟨Fin.elim0,Fin.elim0,by simp⟩
  | succ r =>
      by_contra! h
      have hh := HTGeometry.finrank_span_rows_le_of_minors M r h
      have hk := M.rank_eq_finrank_span_row.le.trans hh
      omega

private theorem order_le_rank {K : Type*} [Field K] (M : Matrix (Fin a) (Fin b) K) {r : ℕ}
    (i : Fin r → Fin a) (j : Fin r → Fin b) (hn : (M.submatrix i j).det≠0) : r≤M.rank := by
  cases r with
  | zero => exact Nat.zero_le _
  | succ r => exact (HTGeometry.lt_finrank_span_rows_of_minor M i j hn).trans_le M.rank_eq_finrank_span_row.ge

/-- One nonzero polynomial minor suffices: everywhere off its zero set,
the rank attains its global maximum among all specializations over R. -/
theorem polynomial_maximal_minor_certificate {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (hf : Function.Injective f)
    (P : Matrix (Fin a) (Fin b) (MvPolynomial (Fin n) R)) :
    ∃ (r : ℕ) (i : Fin r → Fin a) (j : Fin r → Fin b), (P.submatrix i j).det≠0 ∧
      (∀ x, (polynomialFieldMatrix f P x).rank≤r) ∧
      (∀ x, MvPolynomial.eval x (P.submatrix i j).det≠0 → (polynomialFieldMatrix f P x).rank=r) := by
  obtain ⟨x,top⟩ := maximal_rank_point (polynomialFieldMatrix f P)
  let M := polynomialFieldMatrix f P x
  obtain ⟨i,j,hm⟩ := maximal_minor M
  have hx := (fieldMinor_zero_iff f hf P x i j).not.mp hm
  refine ⟨M.rank,i,j,fun h => hx (by rw [h,map_zero]),top,fun y hy => ?_⟩
  exact le_antisymm (top y) (order_le_rank _ i j ((fieldMinor_zero_iff f hf P y i j).not.mpr hy))

/-- One fixed symbolic minor is generically nonzero. At every integral
point where it survives, the matrix has maximum rank on the entire box. -/
theorem padic_maximal_minor_certificate (P : Matrix (Fin a) (Fin b) (MvPolynomial (Fin n) ℤ_[p])) :
    ∃ (r : ℕ) (i : Fin r → Fin a) (j : Fin r → Fin b),
      (P.submatrix i j).det≠0 ∧
      (∀ x, (padicFieldMatrix p P x).rank≤r) ∧
      (∀ x, MvPolynomial.eval x (P.submatrix i j).det≠0 → (padicFieldMatrix p P x).rank=r) ∧
      (∀ᵐ x ∂integralCoordinateHaar p n, MvPolynomial.eval x (P.submatrix i j).det≠0) := by
  obtain ⟨r,i,j,hn,ht,he⟩ := polynomial_maximal_minor_certificate
    (PadicInt.Coe.ringHom (p:=p)) Subtype.coe_injective P
  refine ⟨r,i,j,hn,ht,he,?_⟩
  rw [ae_iff]
  simpa using padic_polynomial_zero_null p n _ hn

/-- The same fixed minor is generically invertible on the entire p-adic
affine space, including slices with arbitrary field-valued coefficients. -/
theorem full_padic_affine_rank_stratum (P : Matrix (Fin a) (Fin b) (MvPolynomial (Fin n) ℚ_[p])) :
    ∃ (r : ℕ) (i : Fin r → Fin a) (j : Fin r → Fin b),
      (P.submatrix i j).det≠0 ∧ (∀ y, (P.map (MvPolynomial.eval y)).rank≤r) ∧
      (∀ᵐ x ∂ RHTower.fieldOnePadicProductUnitBallNormalizedHaar (ι:=Fin n) (fun _ => p),
        (P.map (MvPolynomial.eval x)).rank=r ∧ ((P.map (MvPolynomial.eval x)).submatrix i j).det≠0) := by
  obtain ⟨r,i,j,hn,ht,he⟩ := polynomial_maximal_minor_certificate (RingHom.id ℚ_[p]) Function.injective_id P
  refine ⟨r,i,j,hn,ht,?_⟩
  have hnull := mvPolynomial_product_null n (fun _ => RHTower.fieldOnePadicUnitBallNormalizedHaar p) _ hn
  have ha : ∀ᵐ x ∂ RHTower.fieldOnePadicProductUnitBallNormalizedHaar (ι:=Fin n) (fun _ => p),
      MvPolynomial.eval x (P.submatrix i j).det≠0 := by
    rw [ae_iff]
    simpa only [RHTower.fieldOnePadicProductUnitBallNormalizedHaar, not_not] using hnull
  filter_upwards [ha] with x hx
  exact ⟨he x hx,(fieldMinor_zero_iff (RingHom.id ℚ_[p]) Function.injective_id P x i j).not.mpr hx⟩

/-- On almost every point of an affine coadjoint slice, the common kernel
of the bracket equations has minimum dimension among all points of that slice. -/
theorem ae_affine_padic_minimal_stabilizer
    (A : Matrix (Fin a) (Fin b) ℤ_[p]) (B : Fin n → Matrix (Fin a) (Fin b) ℤ_[p]) :
    let M := padicFieldMatrix p (affinePadicPencil p A B)
    ∀ᵐ x ∂integralCoordinateHaar p n, ∀ y,
      Module.finrank ℚ_[p] (LinearMap.ker (M x).mulVecLin) ≤
        Module.finrank ℚ_[p] (LinearMap.ker (M y).mulVecLin) := by
  let P := affinePadicPencil p A B
  obtain ⟨r,i,j,_,hmax,he,ha⟩ := padic_maximal_minor_certificate p P
  filter_upwards [ha] with x hx y
  have hr := he x hx
  have hy := hmax y
  have ranknull (z : Fin n → ℤ_[p]) : (padicFieldMatrix p P z).rank +
      Module.finrank ℚ_[p] (LinearMap.ker (padicFieldMatrix p P z).mulVecLin)=b := by
    simpa only [Matrix.rank,Module.finrank_pi,Fintype.card_fin] using
      (padicFieldMatrix p P z).mulVecLin.finrank_range_add_finrank_ker
  have xx := ranknull x
  have yy := ranknull y
  change Module.finrank ℚ_[p] (LinearMap.ker (padicFieldMatrix p P x).mulVecLin) ≤
    Module.finrank ℚ_[p] (LinearMap.ker (padicFieldMatrix p P y).mulVecLin)
  omega

end
end GaloisForLFunctions.RepresentationLifting
