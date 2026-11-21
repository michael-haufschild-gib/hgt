import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.FieldDeterminant

/-! # Polynomial normalization at a pair of coalescing energies -/
open Matrix Polynomial Finset
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section
variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]

/-- Twice the determinant in midpoint and half-gap units, extended to
gap zero by removing the first two field coefficients. The field vector
can itself take values in a polynomial ring. -/
def rescaledDet (H : Matrix I I R) (E g : I → R) (s t : I) (b r z : R) : R :=
  let A := scalar I (b+r*z)-H
  let tail := (fieldDet A (diagonal g)).divX.divX
  2*(z^2-1)*(∏ j ∈ (univ.erase s).erase t, (b+r*z-E j)) + tail.eval r + tail.eval (-r)

private theorem pair_product (E : I → R) (s t : I) (hst : s≠t) (b r z : R)
    (hs : E s=b+r) (ht : E t=b-r) :
    (∏ j, (b+r*z-E j)) =
      r^2*(z^2-1)*(∏ j ∈ (univ.erase s).erase t, (b+r*z-E j)) := by
  rw [←mul_prod_erase _ _ (mem_univ s),
    ←mul_prod_erase _ _ (mem_erase.mpr ⟨hst.symm,mem_univ t⟩),hs,ht]
  ring

/-- At a nonzero half-gap the roots are those of the original matrix in
rescaled variables. Field reflection cancels the odd field terms. -/
theorem rescaled_identity (H : Matrix I I R) (E g : I → R) (s t : I) (hst : s≠t) (b r z : R)
    (hs : E s=b+r) (ht : E t=b-r)
    (hchar : (scalar I (b+r*z)-H).det=∏ j, (b+r*z-E j))
    (hrefl : (scalar I (b+r*z)-H + (-r) • diagonal g).det =
      (scalar I (b+r*z)-H + r • diagonal g).det) :
    r^2 * rescaledDet H E g s t b r z = 2*(scalar I (b+r*z)-H + r • diagonal g).det := by
  let A := scalar I (b+r*z)-H
  let p := fieldDet A (diagonal g)
  have h := symmetrized_quadratic p r
  have h0 : p.coeff 0=A.det := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp only [p,eval_fieldDet,zero_smul,add_zero]
  have hp : p.eval r=(A+r • diagonal g).det := eval_fieldDet _ _ _
  have hn : p.eval (-r)=(A+r • diagonal g).det := (eval_fieldDet _ _ _).trans hrefl
  rw [hp,hn,h0,hchar,pair_product E s t hst b r z hs ht] at h
  change r^2*(2*(z^2-1)*_+p.divX.divX.eval r+p.divX.divX.eval (-r))=2*(A+r • diagonal g).det
  linear_combination -h

/-- At the classical doublet the normalization leaves the two-level
polynomial z²−1−gₛ² and the product of the spectator gaps. -/
theorem rescaled_diagonal (E g : I → R) (s t : I) (hst : s≠t)
    (hE : E s=E t) (hg : g t= -g s) (z : R) :
    rescaledDet (diagonal E) E g s t (E s) 0 z =
      2*(∏ j ∈ (univ.erase s).erase t, (E s-E j))*(z^2-1-(g s)^2) := by
  have hA : scalar I (E s)-diagonal E=diagonal (fun j => E s-E j) := by
    ext i j
    by_cases h : i=j
    · subst j; simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply,h]
  simp only [rescaledDet,zero_mul,add_zero,neg_zero,hA,quadratic_at_zero]
  rw [doublet_quadratic_coeff (fun j => E s-E j) g s t hst (sub_self _) (sub_eq_zero.mpr hE) hg]
  ring

private theorem map_fieldDet {S : Type*} [CommRing S] (φ : R →+* S) (A B : Matrix I I R) :
    (fieldDet A B).map φ = fieldDet (A.map φ) (B.map φ) := by
  change (Polynomial.mapRingHom φ) _ = _
  rw [fieldDet,fieldDet,RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change ((C (A i j) + Polynomial.X*C (B i j)).map φ) = _
  simp [Matrix.map_apply,Matrix.smul_apply,smul_eq_mul]

private theorem map_divX' {S : Type*} [CommRing S] (φ : R →+* S) (p : R[X]) :
    p.divX.map φ=(p.map φ).divX := by
  ext k
  simp only [coeff_divX,coeff_map]

private theorem map_tail_eval {S : Type*} [CommRing S] (φ : R →+* S) (A B : Matrix I I R) (r : R) :
    φ ((fieldDet A B).divX.divX.eval r) =
      (fieldDet (A.map φ) (B.map φ)).divX.divX.eval (φ r) := by
  rw [←Polynomial.eval₂_hom,←Polynomial.eval_map,map_divX',map_divX',map_fieldDet]

/-- Normalization commutes with coefficient specialization, including
specialization at a collision. No inverse gap enters this identity. -/
theorem map_rescaledDet {S : Type*} [CommRing S] (φ : R →+* S) (H : Matrix I I R) (E g : I → R)
    (s t : I) (b r z : R) : φ (rescaledDet H E g s t b r z) =
      rescaledDet (H.map φ) (fun i => φ (E i)) (fun i => φ (g i)) s t (φ b) (φ r) (φ z) := by
  have ha : (scalar I (b+r*z)-H).map φ = scalar I (φ b+φ r*φ z)-H.map φ := by
    ext i j
    by_cases h : i=j
    · subst j; simp [Matrix.map_apply,Matrix.scalar_apply]
    · simp [Matrix.map_apply,Matrix.scalar_apply,h]
  have hb : (diagonal g).map φ = diagonal (fun i => φ (g i)) := by
    ext i j
    by_cases h : i=j
    · subst j; simp [Matrix.map_apply]
    · simp [Matrix.map_apply,Matrix.diagonal_apply_ne _ h]
  simp only [rescaledDet,map_add φ,map_mul φ,map_sub φ,map_pow φ,map_ofNat φ,map_one φ,map_prod,
    map_tail_eval,ha,hb,map_neg φ]

#print axioms rescaled_identity
#print axioms rescaled_diagonal
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
