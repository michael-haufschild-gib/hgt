import GaloisForLFunctions.HTGeometry.ObserverTriangleInequality

/-!
# The distance between observer metrics is symmetric

Measuring the second metric in the frame of the first gives the same number as measuring the first
in the frame of the second.  The mechanism is that the relative form of the reversed pair is
carried onto the inverse of the relative form by the same operator that intertwines `X* X` with
`X X*`: if `G = X* X` has the orthonormal eigenframe `u` with weights `g`, then the normalised
images `g i ^ (-1/2) • X (u i)` are an orthonormal eigenframe of `X X*` with the same weights.
Since inversion negates the logarithm, the two distances agree.

Together with `observerDist_eq_zero_iff` and `observerDist_triangle`, this makes the space of
positive-definite Hermitian forms a metric space.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## An orthonormal family of full cardinality is a frame -/

/-- **An orthonormal family indexed by the dimension is an orthonormal frame.** -/
noncomputable def orthonormalBasisOfCard (hn : finrank ℂ E = n) {v : Fin n → E}
    (hv : Orthonormal ℂ v) : OrthonormalBasis (Fin n) ℂ E :=
  OrthonormalBasis.mk hv (by
    rw [top_le_iff]
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_fin, hn])

theorem coe_orthonormalBasisOfCard (hn : finrank ℂ E = n) {v : Fin n → E}
    (hv : Orthonormal ℂ v) (i : Fin n) : orthonormalBasisOfCard hn hv i = v i := by
  rw [orthonormalBasisOfCard, OrthonormalBasis.coe_mk]

/-! ## The distance from an arbitrary diagonalisation -/

/-- **The radial distance read off any orthonormal diagonalisation.** -/
theorem distId_eq_sqrt_of_diagonal (b : OrthonormalBasis (Fin n) ℂ E) (hn : finrank ℂ E = n)
    {f : E →ₗ[ℂ] E} (hf : f.IsSymmetric) {d : Fin n → ℝ}
    (hd : ∀ i, f (b i) = ((d i : ℝ) : ℂ) • b i) (hpos : ∀ i, 0 < d i) :
    distId hf hn = Real.sqrt (∑ i, Real.log (d i) ^ 2) := by
  rw [distId, logOp_eq_of_diagonal b hn hf hd hpos,
    hsNorm_toCLM_diagonal b (diagOp_apply_basis b _)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The radial distance depends only on the operator.** -/
theorem distId_congr {f g : E →ₗ[ℂ] E} (hf : f.IsSymmetric) (hg : g.IsSymmetric)
    (hn : finrank ℂ E = n) (h : f = g) : distId hf hn = distId hg hn := by
  subst h
  rfl

/-! ## Swapping the two factors of a product -/

/-- **The two orders of a product of two Hermitian factors are at the same distance from the
reference metric.**  Writing `X = Y Z`, the operators `X* X = Z Y Y Z` and `X X* = Y Z Z Y` carry
the same weights, on the frame obtained by normalising the images of an eigenframe. -/
theorem distId_swap {Y Z G H : E →ₗ[ℂ] E} (hY : Y.IsSymmetric) (hZ : Z.IsSymmetric)
    (hn : finrank ℂ E = n) (hG : G.IsSymmetric) (hH : H.IsSymmetric)
    (hGeq : G = Z ∘ₗ (Y ∘ₗ (Y ∘ₗ Z))) (hHeq : H = Y ∘ₗ (Z ∘ₗ (Z ∘ₗ Y)))
    (hGpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (G v)).re) :
    distId hH hn = distId hG hn := by
  classical
  set u := hG.eigenvectorBasis hn with hudef
  set g := hG.eigenvalues hn with hgdef
  have hgpos : ∀ i, 0 < g i := eigenvalues_pos hG hn hGpos
  -- the polarisation identity for the factorisation `G = (YZ)* (YZ)`
  have hpolar : ∀ v w : E, inner ℂ (Y (Z v)) (Y (Z w)) = inner ℂ v (G w) := by
    intro v w
    rw [hGeq]
    rw [hY (Z v) (Y (Z w)), hZ v (Y (Y (Z w)))]
    rfl
  -- the normalised images of the eigenframe
  set c : Fin n → ℝ := fun i => (Real.sqrt (g i))⁻¹ with hcdef
  set w : Fin n → E := fun i => ((c i : ℝ) : ℂ) • Y (Z (u i)) with hwdef
  have hGu : ∀ i, G (u i) = ((g i : ℝ) : ℂ) • u i := hG.apply_eigenvectorBasis hn
  have hinner : ∀ i j, inner ℂ (Y (Z (u i))) (Y (Z (u j)))
      = ((g j : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) := by
    intro i j
    rw [hpolar, hGu j, inner_smul_right, orthonormal_iff_ite.1 u.orthonormal i j]
  have hcsq : ∀ i, c i * (c i * g i) = 1 := by
    intro i
    have hsq : Real.sqrt (g i) * Real.sqrt (g i) = g i :=
      Real.mul_self_sqrt (le_of_lt (hgpos i))
    have hne : Real.sqrt (g i) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hgpos i))
    have hkey : (Real.sqrt (g i))⁻¹
        * ((Real.sqrt (g i))⁻¹ * (Real.sqrt (g i) * Real.sqrt (g i))) = 1 := by
      field_simp
    rw [hsq] at hkey
    exact hkey
  have hw : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]
    intro i j
    have hcast : inner ℂ (w i) (w j)
        = ((c i : ℝ) : ℂ) * (((c j : ℝ) : ℂ)
          * (((g j : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0))) := by
      show inner ℂ (((c i : ℝ) : ℂ) • Y (Z (u i))) (((c j : ℝ) : ℂ) • Y (Z (u j))) = _
      rw [inner_smul_left, inner_smul_right, hinner i j, Complex.conj_ofReal]
    rw [hcast]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, mul_one]
      rw [show ((c i : ℝ) : ℂ) * (((c i : ℝ) : ℂ) * ((g i : ℝ) : ℂ))
          = ((c i * (c i * g i) : ℝ) : ℂ) from by push_cast; ring, hcsq i, Complex.ofReal_one]
    · rw [if_neg hij, mul_zero, mul_zero, mul_zero]
  set b := orthonormalBasisOfCard hn hw with hbdef
  have hHb : ∀ i, H (b i) = ((g i : ℝ) : ℂ) • b i := by
    intro i
    rw [hbdef, coe_orthonormalBasisOfCard, hwdef]
    simp only
    rw [map_smul, smul_comm]
    congr 1
    show H (Y (Z (u i))) = ((g i : ℝ) : ℂ) • Y (Z (u i))
    have hHX : H (Y (Z (u i))) = Y (Z (G (u i))) := by
      rw [hHeq, hGeq]
      rfl
    rw [hHX, hGu i, map_smul, map_smul]
  rw [distId_eq_sqrt_of_diagonal b hn hH hHb hgpos, distId_eq_sqrt hG hn, ← hgdef]

/-! ## Symmetry of the distance between observer metrics -/

variable {P Q : E →ₗ[ℂ] E}

/-- **The relative form of the reversed pair inverts the relative form.** -/
theorem relOp_swap_eq_invOp (hP : P.IsSymmetric) (hQ : Q.IsSymmetric) (hn : finrank ℂ E = n)
    (hPpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re)
    (hQpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (Q v)).re) :
    sqrtOp hP hn ∘ₗ (invSqrtOp hQ hn ∘ₗ (invSqrtOp hQ hn ∘ₗ sqrtOp hP hn))
      = invOp (isSymmetric_relOp hP hn hQ) hn := by
  have hsqP : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (sqrtOp hP hn v)).re :=
    fun v hv => inner_sqrtOp_pos hP hn hPpos hv
  have hsqQ : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (sqrtOp hQ hn v)).re :=
    fun v hv => inner_sqrtOp_pos hQ hn hQpos hv
  have hApos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (relOp hP hn Q v)).re :=
    fun v hv => inner_relOp_pos hP hn hPpos hQ hQpos hv
  refine LinearMap.ext fun v => ?_
  have hAG : relOp hP hn Q
      (sqrtOp hP hn (invSqrtOp hQ hn (invSqrtOp hQ hn (sqrtOp hP hn v)))) = v := by
    show invSqrtOp hP hn (Q (invSqrtOp hP hn
      (sqrtOp hP hn (invSqrtOp hQ hn (invSqrtOp hQ hn (sqrtOp hP hn v)))))) = v
    rw [invSqrtOp, invOp_comp (isSymmetric_sqrtOp hP hn) hn hsqP,
      show Q (invSqrtOp hQ hn (invSqrtOp hQ hn (sqrtOp hP hn v)))
        = sqrtOp hQ hn (sqrtOp hQ hn (invSqrtOp hQ hn (invSqrtOp hQ hn (sqrtOp hP hn v)))) from
        (sqrtOp_comp_sqrtOp hQ hn hQpos _).symm,
      invSqrtOp, comp_invOp (isSymmetric_sqrtOp hQ hn) hn hsqQ,
      comp_invOp (isSymmetric_sqrtOp hQ hn) hn hsqQ,
      invOp_comp (isSymmetric_sqrtOp hP hn) hn hsqP]
  have := invOp_comp (isSymmetric_relOp hP hn hQ) hn hApos
    (sqrtOp hP hn (invSqrtOp hQ hn (invSqrtOp hQ hn (sqrtOp hP hn v))))
  rw [hAG] at this
  show sqrtOp hP hn (invSqrtOp hQ hn (invSqrtOp hQ hn (sqrtOp hP hn v)))
    = invOp (isSymmetric_relOp hP hn hQ) hn v
  exact this.symm

/-- **The distance between observer metrics is symmetric.**  With `observerDist_eq_zero_iff` and
`observerDist_triangle` this makes the positive-definite Hermitian forms a metric space. -/
theorem observerDist_comm (hP : P.IsSymmetric) (hQ : Q.IsSymmetric) (hn : finrank ℂ E = n)
    (hPpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (P v)).re)
    (hQpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (Q v)).re) :
    observerDist hP hn hQ = observerDist hQ hn hP := by
  have hApos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (relOp hP hn Q v)).re :=
    fun v hv => inner_relOp_pos hP hn hPpos hQ hQpos hv
  set G : E →ₗ[ℂ] E :=
    sqrtOp hP hn ∘ₗ (invSqrtOp hQ hn ∘ₗ (invSqrtOp hQ hn ∘ₗ sqrtOp hP hn)) with hGdef
  have hGinv : G = invOp (isSymmetric_relOp hP hn hQ) hn :=
    relOp_swap_eq_invOp hP hQ hn hPpos hQpos
  have hGsym : G.IsSymmetric := by
    rw [hGinv]
    exact isSymmetric_invOp (isSymmetric_relOp hP hn hQ) hn
  have hGpos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (G v)).re := by
    intro v hv
    rw [hGinv]
    exact inner_invOp_pos (isSymmetric_relOp hP hn hQ) hn hApos hv
  have hHeq : relOp hQ hn P
      = invSqrtOp hQ hn ∘ₗ (sqrtOp hP hn ∘ₗ (sqrtOp hP hn ∘ₗ invSqrtOp hQ hn)) := by
    refine LinearMap.ext fun v => ?_
    show invSqrtOp hQ hn (P (invSqrtOp hQ hn v)) = _
    rw [← sqrtOp_comp_sqrtOp hP hn hPpos]
    rfl
  calc observerDist hP hn hQ
      = distId (isSymmetric_relOp hP hn hQ) hn := rfl
    _ = distId hGsym hn := by
        rw [distId_congr hGsym (isSymmetric_invOp (isSymmetric_relOp hP hn hQ) hn) hn hGinv,
          distId_invOp (isSymmetric_relOp hP hn hQ) hn hApos]
    _ = distId (isSymmetric_relOp hQ hn hP) hn :=
        (distId_swap (isSymmetric_invSqrtOp hQ hn) (isSymmetric_sqrtOp hP hn) hn hGsym
          (isSymmetric_relOp hQ hn hP) hGdef hHeq hGpos).symm
    _ = observerDist hQ hn hP := rfl

end GaloisForLFunctions.HTGeometry
