import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.ProductInputs.ProjectorTransport

/-! # Compression to a marked column of a unitary basis -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenlineSignals
noncomputable section
open SpanningDensity.ProductInputs

variable {d : Type*} [Fintype d] [DecidableEq d]
private abbrev Mat (d : Type*) := Matrix d d ℂ

/-- Orthogonal projection onto column r. -/
def marked (V : Matrix.unitaryGroup d ℂ) (r : d) := V.val*basisProjector r*star V.val

/-- Expectation of X in column r. -/
def expectation (V : Matrix.unitaryGroup d ℂ) (r : d) (X : Mat d) : ℂ :=
  (star V.val*X*V.val) r r

private theorem basis_self (r : d) : star (basisProjector r)=basisProjector r := by
  change (diagonal _)ᴴ=_
  rw [diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i=r <;> simp [h]

theorem marked_self (V : Matrix.unitaryGroup d ℂ) (r : d) : star (marked V r)=marked V r := by
  simp only [marked,star_mul,star_star,basis_self,mul_assoc]

theorem marked_square (V : Matrix.unitaryGroup d ℂ) (r : d) : marked V r*marked V r=marked V r := by
  have hb : basisProjector r*basisProjector r=basisProjector r := by
    rw [basisProjector,diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : i=r <;> simp [h]
  have he := (Unitary.mem_iff.mp V.property).1
  calc _ = V.val*(basisProjector r*(star V.val*V.val)*basisProjector r)*star V.val := by simp only [marked,mul_assoc]
       _ = _ := by rw [he,mul_one,hb]; rfl

theorem marked_norm (V : Matrix.unitaryGroup d ℂ) (r : d) : ‖marked V r‖=1 := by
  rw [marked,CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem V.property),
    CStarRing.norm_mem_unitary_mul _ V.property,basisProjector,Matrix.l2_opNorm_diagonal]
  let f (i : d) : ℂ := if i=r then 1 else 0
  change ‖f‖=1
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    by_cases h : i=r <;> simp [f,h]
  · simpa [f] using (norm_le_pi_norm f r)

theorem marked_sandwich_zero (V : Matrix.unitaryGroup d ℂ) (r : d) (X : Mat d)
    (hx : expectation V r X=0) : marked V r*X*marked V r=0 := by
  let Y := star V.val*X*V.val
  have h : basisProjector r*Y*basisProjector r=0 := by
    ext i j
    by_cases hi : i=r <;> by_cases hj : j=r <;>
      simp [basisProjector,mul_diagonal,diagonal_mul,hi,hj,show Y r r=0 from hx]
  calc _ = V.val*(basisProjector r*Y*basisProjector r)*star V.val := by simp only [marked,Y,mul_assoc]
       _ = _ := by rw [h,mul_zero,zero_mul]

theorem expectation_real (V : Matrix.unitaryGroup d ℂ) (r : d) (X : Mat d)
    (hx : IsSelfAdjoint X) : ((expectation V r X).re:ℂ)=expectation V r X := by
  have he : IsSelfAdjoint (star V.val*X*V.val) := by
    change star _=_
    simp only [star_mul,star_star,hx.star_eq,mul_assoc]
  exact he.isHermitian.coe_re_apply_self r

end
end GaloisForLFunctions.HTGeometry.EigenlineSignals
