import GaloisForLFunctions.HTGeometry.MomentRealRootedness
import GaloisForLFunctions.HTGeometry.MomentFiniteCoordinateValue

/-!
# Real and simple roots at a finite Hankel boundary
-/

open scoped BigOperators
open Matrix Polynomial

namespace HTGeometry

noncomputable section

/-- Bilinear finite-coordinate form of the moment inner product. -/
theorem momentInner_ofFn_ofFn
    (s : ℕ → ℝ) (n : ℕ) (a b : Fin n → ℝ) :
    momentInner s (Polynomial.ofFn n a) (Polynomial.ofFn n b) =
      a ⬝ᵥ (momentHankelMatrix s n).mulVec b := by
  rw [momentInner_def, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.ofFn_eq_sum_monomial, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [momentFunctional_finset_sum]
  simp_rw [momentFunctional_finset_sum]
  simp only [dotProduct, Matrix.mulVec, momentHankelMatrix, Finset.mul_sum,
    Polynomial.monomial_mul_monomial, momentFunctional_monomial]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A positive finite Hankel block is strictly positive on every nonzero polynomial visible in
that block. -/
theorem momentInner_self_pos_of_natDegree_lt
    {s : ℕ → ℝ} {n : ℕ} (hpos : (momentHankelMatrix s n).PosDef)
    {p : Polynomial ℝ} (hp : p ≠ 0) (hdeg : p.natDegree < n) :
    0 < momentInner s p p := by
  let a : Fin n → ℝ := Polynomial.toFn n p
  have hpof : Polynomial.ofFn n a = p :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg
  have ha : a ≠ 0 := by
    intro ha
    apply hp
    rw [← hpof, ha, Polynomial.ofFn_zero]
  have hquad := hpos.dotProduct_mulVec_pos ha
  rw [star_trivial, ← momentInner_ofFn_ofFn, hpof] at hquad
  exact hquad

/-- Coefficient polynomial of a finite Hankel vector. -/
def finiteHankelNullPolynomial {n : ℕ} (c : Fin n → ℝ) : Polynomial ℝ :=
  Polynomial.ofFn n c

/-- A Hankel kernel vector is orthogonal to every polynomial represented in the same finite
coordinate block. -/
theorem momentInner_finiteHankelNullPolynomial_eq_zero_of_kernel
    {s : ℕ → ℝ} {n : ℕ} {c : Fin n → ℝ}
    (hc : momentHankelMatrix s n *ᵥ c = 0)
    {q : Polynomial ℝ} (hq : q.natDegree < n) :
    momentInner s (finiteHankelNullPolynomial c) q = 0 := by
  let b : Fin n → ℝ := Polynomial.toFn n q
  have hqof : Polynomial.ofFn n b = q :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hq
  rw [momentInner_comm, ← hqof, finiteHankelNullPolynomial,
    momentInner_ofFn_ofFn, hc, dotProduct_zero]

/-- A full-degree finite Hankel null polynomial has its advertised degree. -/
theorem finiteHankelNullPolynomial_natDegree
    {n : ℕ} (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0) :
    (finiteHankelNullPolynomial c).natDegree = n := by
  apply Nat.le_antisymm
  · exact Nat.le_of_lt_succ
      (Polynomial.ofFn_natDegree_lt (Nat.succ_pos n) c)
  · apply Polynomial.le_natDegree_of_ne_zero
    change (Polynomial.ofFn (n + 1) c).coeff n ≠ 0
    rw [Polynomial.ofFn_coeff_eq_val_of_lt c (Nat.lt_succ_self n)]
    exact hlast

theorem finiteHankelNullPolynomial_ne_zero
    {n : ℕ} (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0) :
    finiteHankelNullPolynomial c ≠ 0 := by
  intro hp
  apply hlast
  have hc0 : c = 0 := by
    apply Polynomial.injective_ofFn (n + 1)
    simpa [finiteHankelNullPolynomial] using hp
  exact congrFun hc0 (Fin.last n)

/-- **Finite-boundary real-rootedness.**  A full-degree null polynomial of a singular Hankel block
whose preceding block is positive definite has no nonreal root. -/
theorem finiteHankelNullPolynomial_aeval_ne_zero
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) {z : ℂ} (hz : z.im ≠ 0) :
    Polynomial.aeval z (finiteHankelNullPolynomial c) ≠ 0 := by
  intro hroot
  let p := finiteHankelNullPolynomial c
  obtain ⟨g, hpg⟩ := conjQuadratic_dvd_of_aeval_eq_zero p hz hroot
  have hpne : p ≠ 0 := finiteHankelNullPolynomial_ne_zero c hlast
  have hgne : g ≠ 0 := by
    intro hg
    rw [hg, mul_zero] at hpg
    exact hpne hpg
  have hpdeg : p.natDegree = n := finiteHankelNullPolynomial_natDegree c hlast
  have hnd : n = 2 + g.natDegree := by
    rw [← hpdeg, hpg, natDegree_mul (conjQuadratic_ne_zero z) hgne,
      conjQuadratic_natDegree]
  have hglt : g.natDegree < n + 1 := by omega
  have hzero : momentInner s p g = 0 := by
    exact momentInner_finiteHankelNullPolynomial_eq_zero_of_kernel hc hglt
  have hpoly : conjQuadratic z * g * g =
      ((X - C z.re) * g) * ((X - C z.re) * g) + (z.im ^ 2) • (g * g) := by
    simp only [conjQuadratic, Polynomial.smul_eq_C_mul]
    ring
  have hexp : momentInner s p g =
      momentInner s ((X - C z.re) * g) ((X - C z.re) * g) +
        z.im ^ 2 * momentInner s g g := by
    rw [hpg, momentInner_def, hpoly, momentFunctional_add, momentFunctional_smul,
      momentInner_def, momentInner_def]
  have hgdeg : g.natDegree < n := by omega
  have hxgne : (X - C z.re) * g ≠ 0 := mul_ne_zero (X_sub_C_ne_zero z.re) hgne
  have hxgdeg : ((X - C z.re) * g).natDegree < n := by
    rw [natDegree_mul (X_sub_C_ne_zero z.re) hgne, natDegree_X_sub_C]
    omega
  have h1 : 0 < momentInner s ((X - C z.re) * g) ((X - C z.re) * g) :=
    momentInner_self_pos_of_natDegree_lt hhead hxgne hxgdeg
  have h2 : 0 < momentInner s g g :=
    momentInner_self_pos_of_natDegree_lt hhead hgne hgdeg
  have h3 : 0 < z.im ^ 2 := sq_pos_of_ne_zero hz
  rw [hexp] at hzero
  nlinarith

theorem finiteHankelNullPolynomial_root_im_eq_zero
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) {z : ℂ}
    (hz : Polynomial.aeval z (finiteHankelNullPolynomial c) = 0) : z.im = 0 := by
  by_contra hne
  exact finiteHankelNullPolynomial_aeval_ne_zero c hhead hc hlast hne hz

/-- **Finite-boundary root simplicity.**  The same null polynomial has no repeated real factor. -/
theorem finiteHankelNullPolynomial_not_sq_dvd
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) (r : ℝ) :
    ¬ (((X - C r) ^ 2 : Polynomial ℝ) ∣ finiteHankelNullPolynomial c) := by
  rintro ⟨g, hpg⟩
  let p := finiteHankelNullPolynomial c
  have hpgp : p = (X - C r) ^ 2 * g := by simpa only [p] using hpg
  have hpne : p ≠ 0 := finiteHankelNullPolynomial_ne_zero c hlast
  have hgne : g ≠ 0 := by
    intro hg
    rw [hg, mul_zero] at hpg
    exact hpne hpg
  have hpdeg : p.natDegree = n := finiteHankelNullPolynomial_natDegree c hlast
  have hsqne : ((X - C r) ^ 2 : Polynomial ℝ) ≠ 0 :=
    pow_ne_zero 2 (X_sub_C_ne_zero r)
  have hnd : n = 2 + g.natDegree := by
    rw [← hpdeg, hpgp, natDegree_mul hsqne hgne, natDegree_pow,
      natDegree_X_sub_C]
  have hglt : g.natDegree < n + 1 := by omega
  have hzero : momentInner s p g = 0 :=
    momentInner_finiteHankelNullPolynomial_eq_zero_of_kernel hc hglt
  have hxgne : (X - C r) * g ≠ 0 := mul_ne_zero (X_sub_C_ne_zero r) hgne
  have hxgdeg : ((X - C r) * g).natDegree < n := by
    rw [natDegree_mul (X_sub_C_ne_zero r) hgne, natDegree_X_sub_C]
    omega
  have hpos : 0 < momentInner s ((X - C r) * g) ((X - C r) * g) :=
    momentInner_self_pos_of_natDegree_lt hhead hxgne hxgdeg
  have hexp : momentInner s p g =
      momentInner s ((X - C r) * g) ((X - C r) * g) := by
    rw [hpgp, momentInner_def, momentInner_def]
    congr 1
    ring
  rw [hexp] at hzero
  exact (ne_of_gt hpos) hzero

theorem finiteHankelNullPolynomial_rootMultiplicity_le_one
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) (r : ℝ) :
    rootMultiplicity r (finiteHankelNullPolynomial c) ≤ 1 := by
  by_contra hmult
  exact finiteHankelNullPolynomial_not_sq_dvd c hhead hc hlast r
    (dvd_trans (pow_dvd_pow _ (not_le.mp hmult)) (pow_rootMultiplicity_dvd _ _))

end

end HTGeometry
