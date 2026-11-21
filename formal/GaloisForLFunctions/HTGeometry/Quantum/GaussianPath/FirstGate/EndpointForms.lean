import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # The first variation of a pair of conjugate spectral endpoints -/
open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem sum_pair {R : Type*} [AddCommMonoid R] (a b : I) (hab : a≠b) (f : I → R)
    (hf : ∀ k, k≠a → k≠b → f k=0) : ∑ k, f k=f a+f b := by
  have hs := Finset.sum_subset (s₁ := {a,b}) (s₂ := Finset.univ) (f := f) (Finset.subset_univ _) (by
    intro k _ hk
    have h : k≠a ∧ k≠b := by simpa using hk
    exact hf k h.1 h.2)
  simpa [hab] using hs.symm

/-- The excess of the real overlap over the arc endpoint value is a
weighted sum of nonnegative gaps. A minimizing vector has no component
on any phase strictly inside the arc. -/
theorem endpoint_mass (u : I → ℂ) (v : EuclideanSpace ℂ I) (hv : ‖v‖=1)
    (y : ℝ) (hmin : ∀ k, y ≤ (u k).re) :
    let U := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (Matrix.diagonal u)
    y ≤ (⟪U v,v⟫_ℂ).re ∧ ((⟪U v,v⟫_ℂ).re=y → ∀ k, y < (u k).re → v k=0) := by
  intro U
  have he : (⟪U v,v⟫_ℂ).re=∑ k, (u k).re*‖v k‖^2 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ k, v k*star ((Matrix.diagonal u *ᵥ WithLp.ofLp v) k)).re=_
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.mulVec_diagonal]
    change (v k*star (u k*v k)).re=_
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.star_def,
      Complex.conj_re,Complex.conj_im]
    ring
  have hw : ∑ k, ‖v k‖^2=1 := by rw [←EuclideanSpace.norm_sq_eq,hv,one_pow]
  have hcalc : ∑ k, ((u k).re-y)*‖v k‖^2=(⟪U v,v⟫_ℂ).re-y := by
    simp only [sub_mul,Finset.sum_sub_distrib,←he,←Finset.mul_sum,hw,mul_one]
  have hn (k : I) : 0≤((u k).re-y)*‖v k‖^2 := mul_nonneg (sub_nonneg.mpr (hmin k)) (sq_nonneg _)
  refine ⟨sub_nonneg.mp (hcalc ▸ Finset.sum_nonneg (fun k _ => hn k)),?_⟩
  intro h k hk
  rw [h,sub_self] at hcalc
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hcalc k (Finset.mem_univ _)
  by_contra hvk
  exact (mul_pos (sub_pos.mpr hk) (pow_pos (norm_pos_iff.mpr hvk) 2)).ne' hz

private theorem endpoint_algebra (u p q w : ℂ) (d : ℝ) :
    ((Complex.I*((d:ℂ)*p+w*q))*star (u*p)).re+
      ((Complex.I*(star w*p-(d:ℂ)*q))*star (star u*q)).re =
      u.im*d*(‖p‖^2+‖q‖^2) := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.add_re,
    Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

/-- On the contact space, conjugate endpoint phases cancel the entire
off-diagonal Hermitian contribution. A positive difference of diagonal
expectations gives a strict improvement in every minimizing direction. -/
theorem endpoint_variation (u : I → ℂ) (A : Matrix I I ℂ) (a b : I) (hab : a≠b)
    (hub : u b=star (u a)) (hs : 0 < (u a).im) {d : ℝ} (hd : 0 < d)
    (ha : A a a=(d:ℂ)) (hb : A b b=-(d:ℂ)) (hcross : A b a=star (A a b))
    (v : EuclideanSpace ℂ I) (hv : ‖v‖=1) (hz : ∀ k, k≠a → k≠b → v k=0) :
    let U := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (Matrix.diagonal u)
    let K := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (Complex.I • A)
    0 < (⟪U v,K v⟫_ℂ).re := by
  intro U K
  let f (j : I) := (Complex.I*((A *ᵥ WithLp.ofLp v) j))*star (u j*v j)
  have hinner : (⟪U v,K v⟫_ℂ).re=(∑ j, f j).re := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (((Complex.I • A) *ᵥ WithLp.ofLp v) ⬝ᵥ star (Matrix.diagonal u *ᵥ WithLp.ofLp v)).re=_
    simp only [Matrix.smul_mulVec,Matrix.mulVec_diagonal,dotProduct,Pi.star_apply,Pi.smul_apply,
      smul_eq_mul,f]
  have hsum : ∑ j, f j=f a+f b := sum_pair a b hab f (by
    intro j hja hjb
    simp only [f,hz j hja hjb,mul_zero,star_zero])
  have hv' (j : I) : (A *ᵥ WithLp.ofLp v) j=A j a*v a+A j b*v b :=
    sum_pair a b hab (fun i => A j i*v i) (fun i hia hib => by rw [hz i hia hib,mul_zero])
  have hp : ‖v a‖^2+‖v b‖^2=1 := by
    rw [←sum_pair a b hab (fun j => ‖v j‖^2) (fun j hja hjb => by simp [hz j hja hjb]),
      ←EuclideanSpace.norm_sq_eq,hv,one_pow]
  rw [hinner,hsum,Complex.add_re]
  dsimp only [f]
  rw [hv' a,hv' b,ha,hb,hcross,hub,neg_mul,←sub_eq_add_neg,endpoint_algebra,hp,mul_one]
  exact mul_pos hs hd

#print axioms endpoint_mass
#print axioms endpoint_variation
end
end GaloisForLFunctions.HTGeometry.FirstGate
