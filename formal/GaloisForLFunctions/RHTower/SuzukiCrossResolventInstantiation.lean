import Mathlib.Analysis.InnerProductSpace.PiL2
import GaloisForLFunctions.RHTower.SuzukiAntiPickIdentity

/-!
# The cross-resolvent matrix element as a Cauchy combination

A self-adjoint operator with a finite orthonormal eigenbasis has an explicit resolvent: divide each
spectral coefficient by `t j - lambda`.  Its matrix elements between two fixed vectors are therefore
Cauchy combinations, with weights the products of the two vectors' spectral coefficients.

That is what makes a cross-resolvent quotient a ratio of Cauchy transforms in the sense of the
anti-Pick theorem: the weight of a node is `<e, phi_j> <d, phi_j>` and the response is
`<h, phi_j> / <d, phi_j>`.  So the two source-pure spectral statements — nonnegative weights and
monotone responses — are exactly the hypotheses of the anti-Pick theorem, and give the
anti-Herglotz sign of the quotient with nothing further assumed.
-/

namespace RHTower

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The operator with the given orthonormal eigenbasis and eigenvalues. -/
noncomputable def spectralOperator (b : OrthonormalBasis (Fin n) ℝ V) (t : Fin n → ℝ) (v : V) : V :=
  ∑ j, (t j * inner ℝ (b j) v) • b j

/-- The resolvent at `lam` built from the same spectral data. -/
noncomputable def spectralResolvent (b : OrthonormalBasis (Fin n) ℝ V) (t : Fin n → ℝ)
    (lam : ℝ) (v : V) : V :=
  ∑ j, (inner ℝ (b j) v / (t j - lam)) • b j

/-- The basis vectors are eigenvectors. -/
theorem spectralOperator_basis (b : OrthonormalBasis (Fin n) ℝ V) (t : Fin n → ℝ) (i : Fin n) :
    spectralOperator b t (b i) = t i • b i := by
  rw [spectralOperator]
  have hij : ∀ j : Fin n, (t j * inner ℝ (b j) (b i)) • b j
      = if j = i then t i • b i else 0 := by
    intro j
    rw [orthonormal_iff_ite.mp b.orthonormal j i]
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl fun j _ => hij j, Finset.sum_ite_eq' Finset.univ i]
  simp

/-- The spectral coefficient of the resolvent. -/
theorem inner_basis_spectralResolvent (b : OrthonormalBasis (Fin n) ℝ V) (t : Fin n → ℝ)
    (lam : ℝ) (v : V) (i : Fin n) :
    inner ℝ (b i) (spectralResolvent b t lam v) = inner ℝ (b i) v / (t i - lam) :=
  b.orthonormal.inner_right_fintype (fun j => inner ℝ (b j) v / (t j - lam)) i

/-- **It really is the resolvent.**  Off the spectrum, `spectralResolvent` inverts
`spectralOperator - lam`. -/
theorem spectralOperator_spectralResolvent (b : OrthonormalBasis (Fin n) ℝ V) (t : Fin n → ℝ)
    {lam : ℝ} (h : ∀ j, t j ≠ lam) (v : V) :
    spectralOperator b t (spectralResolvent b t lam v) - lam • spectralResolvent b t lam v = v := by
  have hop : spectralOperator b t (spectralResolvent b t lam v)
      = ∑ j, (t j * (inner ℝ (b j) v / (t j - lam))) • b j := by
    rw [spectralOperator]
    exact Finset.sum_congr rfl fun j _ => by rw [inner_basis_spectralResolvent]
  have hsm : lam • spectralResolvent b t lam v
      = ∑ j, (lam * (inner ℝ (b j) v / (t j - lam))) • b j := by
    rw [spectralResolvent, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  rw [hop, hsm, ← Finset.sum_sub_distrib]
  have hterm : ∀ j : Fin n,
      (t j * (inner ℝ (b j) v / (t j - lam))) • b j
        - (lam * (inner ℝ (b j) v / (t j - lam))) • b j = inner ℝ (b j) v • b j := by
    intro j
    rw [← sub_smul]
    congr 1
    have hj : t j - lam ≠ 0 := sub_ne_zero_of_ne (h j)
    field_simp
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  exact b.sum_repr' v

/-- **The matrix element is a Cauchy combination.**  Its weight at each node is the product of the
two vectors' spectral coefficients. -/
theorem inner_spectralResolvent (b : OrthonormalBasis (Fin n) ℝ V) (t : Fin n → ℝ) (lam : ℝ)
    (e d : V) :
    inner ℝ (spectralResolvent b t lam e) d
      = ∑ j, (inner ℝ (b j) e * inner ℝ (b j) d) / (t j - lam) := by
  rw [spectralResolvent, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, div_mul_eq_mul_div]

/-- The cross weight of a node: the product of the two vectors' spectral coefficients. -/
noncomputable def crossWeight (b : OrthonormalBasis (Fin n) ℝ V) (e d : V) (j : Fin n) : ℝ :=
  inner ℝ (b j) e * inner ℝ (b j) d

/-- The response at a node: the ratio of the two spectral coefficients. -/
noncomputable def crossResponse (b : OrthonormalBasis (Fin n) ℝ V) (d h : V) (j : Fin n) : ℝ :=
  inner ℝ (b j) h / inner ℝ (b j) d

/-- A diagonal cross weight is a square, hence nonnegative. -/
theorem crossWeight_self_nonneg (b : OrthonormalBasis (Fin n) ℝ V) (e : V) (j : Fin n) :
    0 ≤ crossWeight b e e j :=
  mul_self_nonneg _

/-- **The denominator of `(6)`.**  The `d`-matrix element is the Cauchy combination with the cross
weights. -/
theorem inner_spectralResolvent_denominator (b : OrthonormalBasis (Fin n) ℝ V) (t : Fin n → ℝ)
    (lam : ℝ) (e d : V) :
    inner ℝ (spectralResolvent b t lam e) d = ∑ j, crossWeight b e d j / (t j - lam) :=
  inner_spectralResolvent b t lam e d

/-- **The numerator of `(6)`.**  Where the `d`-coefficients do not vanish, the `h`-matrix element is
the Cauchy combination with the *weighted responses* — so the quotient has exactly the form the
anti-Pick theorem takes. -/
theorem inner_spectralResolvent_numerator (b : OrthonormalBasis (Fin n) ℝ V) (t : Fin n → ℝ)
    (lam : ℝ) (e d h : V) (hd : ∀ j, inner ℝ (b j) d ≠ 0) :
    inner ℝ (spectralResolvent b t lam e) h
      = ∑ j, (crossWeight b e d j * crossResponse b d h j) / (t j - lam) := by
  rw [inner_spectralResolvent]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [crossWeight, crossResponse]
  have hj := hd j
  field_simp

/-- **The Suzuki instantiation is the anti-Pick theorem.**  Given nonnegative cross weights and
monotone responses — the two source-pure spectral statements — the complexified cross-resolvent
quotient is anti-Herglotz above the real axis.  Nothing else about the operator is used. -/
theorem im_crossResolventRatio_nonpos (b : OrthonormalBasis (Fin n) ℝ V) (t : Fin n → ℝ)
    (e d h : V) {z : ℂ} (hz : 0 < z.im)
    (hw : ∀ j, 0 ≤ crossWeight b e d j)
    (hmono : ∀ j k, 0 ≤ (crossResponse b d h j - crossResponse b d h k) * (t j - t k)) :
    ((∑ j, ((crossWeight b e d j * crossResponse b d h j : ℝ) : ℂ) / ((t j : ℂ) - z)) /
        (∑ j, ((crossWeight b e d j : ℝ) : ℂ) / ((t j : ℂ) - z))).im ≤ 0 :=
  im_shiftRatio_nonpos Finset.univ (crossWeight b e d) (crossResponse b d h) t hz
    (fun j _ => hw j) (fun j _ k _ => hmono j k)

end RHTower
