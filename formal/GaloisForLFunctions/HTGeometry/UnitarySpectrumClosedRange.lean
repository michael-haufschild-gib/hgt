import GaloisForLFunctions.HTGeometry.MixedSpectralTraceEscape
import GaloisForLFunctions.HTGeometry.PhaseResonanceProjection

/-!
# Closed-range law for unitary transgression on the Hilbert–Schmidt ideal

For a unitary `U` of a complex Hilbert space `H`, let `α(T) = U* T U` act on the Hilbert–Schmidt
ideal, modelled as the column space `ℓ²(ι; H)` of a Hilbert basis.  The transgression `δ = 1 - α`
has closed range exactly when the spectrum of `U` is finite.

* Every spectral value of a unitary is unimodular and an approximate eigenvalue: a shifted unitary
  that is bounded below is invertible, since its adjoint is bounded below by the same constant.
* Closed range is the transverse lower bound `c ‖X‖₂ ≤ ‖δ X‖₂` on the Hilbert–Schmidt operators with
  vanishing atomic pinching, the orthogonal complement of the fixed space.
* A finite spectrum makes `U` diagonal with finitely many eigenvalues (continuous functional
  calculus with the spectral indicators), and on the block `P_λ X P_μ` the transgression is the
  scalar `1 - λ̄ μ`; the minimal gap between distinct eigenvalues is a lower bound.
* An infinite spectrum yields either two distinct eigenvalues closer than any `c`, giving the
  rank-one witness `|x⟩⟨y|`, or a nonzero continuous subspace, whose approximate eigenvectors `u`
  give the almost fixed rank-one projection `|u⟩⟨u|`.  Both witnesses are Hilbert–Schmidt orthogonal
  to the fixed space, so the transgression is not bounded below there.
-/

open Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Approximate eigenvalues of a unitary -/

section ApproxPoint

variable {U : H ≃ₗᵢ[ℂ] H}

omit [CompleteSpace H] in
/-- `‖(z̄ - U*) x‖ = ‖(z - U) x‖`: a shifted unitary is normal. -/
theorem norm_conj_smul_sub_symm (U : H ≃ₗᵢ[ℂ] H) (z : ℂ) (x : H) :
    ‖(starRingEnd ℂ) z • x - U.symm x‖ = ‖z • x - U x‖ := by
  have h1 : ‖(starRingEnd ℂ) z • x - U.symm x‖ = ‖(starRingEnd ℂ) z • U x - x‖ := by
    rw [← U.norm_map, map_sub, map_smul, U.apply_symm_apply]
  rw [h1]
  have hre : RCLike.re ⟪(starRingEnd ℂ) z • U x, x⟫_ℂ = RCLike.re ⟪z • x, U x⟫_ℂ := by
    rw [inner_smul_left, inner_smul_left, Complex.conj_conj, ← inner_conj_symm (U x) x]
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hsq : ‖(starRingEnd ℂ) z • U x - x‖ ^ 2 = ‖z • x - U x‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ), norm_smul, norm_smul, Complex.norm_conj,
      U.norm_map, hre]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- **A shifted unitary bounded below is invertible.**  Its range is closed, and its orthogonal
complement is the kernel of the adjoint `z̄ - U*`, which is bounded below by the same constant. -/
theorem not_mem_spectrum_of_boundedBelow {z : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hbd : ∀ x : H, ε * ‖x‖ ≤ ‖z • x - U x‖) : z ∉ spectrum ℂ (unitaryCLM U) := by
  rw [spectrum.mem_iff, not_not]
  set A : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) z - unitaryCLM U
  have hA : ∀ x, A x = z • x - U x := fun x => by
    simp [A, Algebra.algebraMap_eq_smul_one]
  have hzero : ∀ y : H, ε * ‖y‖ ≤ 0 → y = 0 := fun y hy => by
    by_contra h
    have := mul_pos hε (norm_pos_iff.mpr h)
    linarith
  have hinj : Function.Injective A := by
    intro x y hxy
    have h := hbd (x - y)
    rw [smul_sub, map_sub, sub_sub_sub_comm, ← hA, ← hA, hxy, sub_self, norm_zero] at h
    exact sub_eq_zero.mp (hzero _ h)
  have hanti : AntilipschitzWith (Real.toNNReal ε⁻¹) A := by
    refine AddMonoidHomClass.antilipschitz_of_bound _ fun x => ?_
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hε.le), inv_mul_eq_div, le_div_iff₀ hε, mul_comm,
      hA]
    exact hbd x
  have hcl : IsClosed (LinearMap.range (A : H →ₗ[ℂ] H) : Set H) := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
    exact hanti.isClosed_range A.uniformContinuous
  haveI : CompleteSpace (LinearMap.range (A : H →ₗ[ℂ] H)) := hcl.completeSpace_coe
  have hperp : (LinearMap.range (A : H →ₗ[ℂ] H))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have hadj : ∀ x, ⟪A x, y⟫_ℂ = ⟪x, (starRingEnd ℂ) z • y - U.symm y⟫_ℂ := by
      intro x
      rw [hA, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        ← U.inner_map_map x (U.symm y), U.apply_symm_apply]
    have h0 := hy _ ⟨(starRingEnd ℂ) z • y - U.symm y, rfl⟩
    rw [ContinuousLinearMap.coe_coe, hadj, inner_self_eq_zero, sub_eq_zero] at h0
    refine hzero y ?_
    have h := hbd y
    rw [← norm_conj_smul_sub_symm, ← h0, sub_self, norm_zero] at h
    exact h
  have hsurj : Function.Surjective A := by
    have htop := Submodule.orthogonal_eq_bot_iff.mp hperp
    exact LinearMap.range_eq_top.mp htop
  exact isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩

/-- The spectrum of a unitary lies on the unit circle. -/
theorem norm_eq_one_of_mem_spectrum {z : ℂ} (hz : z ∈ spectrum ℂ (unitaryCLM U)) : ‖z‖ = 1 := by
  by_contra h
  refine not_mem_spectrum_of_boundedBelow (ε := |‖z‖ - 1|)
    (abs_pos.mpr (sub_ne_zero.mpr h)) (fun x => ?_) hz
  have h1 := abs_norm_sub_norm_le (z • x) (U x)
  rw [norm_smul, U.norm_map, ← sub_one_mul, abs_mul, abs_norm] at h1
  exact h1

/-- **Spectral values of a unitary are approximate eigenvalues.** -/
theorem exists_approxEigen_of_mem_spectrum {z : ℂ} (hz : z ∈ spectrum ℂ (unitaryCLM U))
    {ε : ℝ} (hε : 0 < ε) : ∃ u : H, ‖u‖ = 1 ∧ ‖U u - z • u‖ ≤ ε := by
  by_contra h
  push Not at h
  refine not_mem_spectrum_of_boundedBelow hε (fun x => ?_) hz
  by_cases hx : x = 0
  · simp [hx]
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖(‖x‖ : ℂ)⁻¹ • x‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hx'.ne']
  have h1 := h _ hu
  have heq : U ((‖x‖ : ℂ)⁻¹ • x) - z • (‖x‖ : ℂ)⁻¹ • x = (‖x‖ : ℂ)⁻¹ • (U x - z • x) := by
    rw [map_smul, smul_sub, smul_comm z]
  rw [heq, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_eq_div,
    lt_div_iff₀ hx', norm_sub_rev] at h1
  exact h1.le

/-- A unitary of a nonzero Hilbert space has approximate eigenvectors with unimodular
approximate eigenvalues. -/
theorem hasApproxEigenvectors_of_nontrivial [Nontrivial H] (U : H ≃ₗᵢ[ℂ] H) :
    HasApproxEigenvectors U := by
  obtain ⟨z, hz⟩ := spectrum.nonempty (unitaryCLM U)
  intro ε hε
  obtain ⟨u, hu, hclose⟩ := exists_approxEigen_of_mem_spectrum hz hε
  exact ⟨u, z, hu, norm_eq_one_of_mem_spectrum hz, hclose⟩

/-- An eigenvalue of a unitary is a spectral value. -/
theorem mem_spectrum_of_mem_pointSpectrum {c : ℂ} (hc : c ∈ unitaryPointSpectrum U) :
    c ∈ spectrum ℂ (unitaryCLM U) := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  rw [spectrum.mem_iff, isUnit_iff_bijective]
  rintro ⟨hinj, -⟩
  refine hx0 (hinj ?_)
  simp [Algebra.algebraMap_eq_smul_one, mem_unitaryEigenspace.mp hx]

end ApproxPoint

/-! ### Rank-one witnesses -/

section RankOne

variable {U : H ≃ₗᵢ[ℂ] H}

/-- An approximate eigenvector `u` makes the rank-one projection `|u⟩⟨u|` almost fixed:
`‖α(|u⟩⟨u|) - |u⟩⟨u|‖₂ ≤ 2 ‖U u - w u‖`. -/
theorem hsNorm_transgression_rankOne_le {u : H} {w : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) {ε : ℝ}
    (hclose : ‖U u - w • u‖ ≤ ε) :
    (hsConj U (InnerProductSpace.rankOne ℂ u u) - InnerProductSpace.rankOne ℂ u u).hsNorm ≤
      2 * ε := by
  set v := w • U.symm u
  have hv : ‖v‖ = 1 := by rw [norm_smul, hw, LinearIsometryEquiv.norm_map, hu, one_mul]
  have hvu : ‖v - u‖ ≤ ε := by
    have : v - u = U.symm (w • u - U u) := by
      rw [map_sub, map_smul, LinearIsometryEquiv.symm_apply_apply]
    rw [this, LinearIsometryEquiv.norm_map, norm_sub_rev]
    exact hclose
  have hdecomp : hsConj U (InnerProductSpace.rankOne ℂ u u) - InnerProductSpace.rankOne ℂ u u =
      InnerProductSpace.rankOne ℂ (v - u) v + InnerProductSpace.rankOne ℂ u (v - u) := by
    rw [hsConj_rankOne, ← rankOne_smul_unimodular (U.symm u) hw, map_sub, map_sub]
    show InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ u u =
      InnerProductSpace.rankOne ℂ v v - InnerProductSpace.rankOne ℂ u v +
        (InnerProductSpace.rankOne ℂ u v - InnerProductSpace.rankOne ℂ u u)
    abel
  rw [hdecomp]
  refine (hsNorm_add_le (isHilbertSchmidt_rankOne (v - u) v)
    (isHilbertSchmidt_rankOne u (v - u))).trans ?_
  rw [hsNorm_rankOne, hsNorm_rankOne, hv, hu, mul_one, one_mul]
  linarith

omit [CompleteSpace H] in
/-- On eigenvectors, conjugation acts on `|x⟩⟨y|` by the phase ratio `λ̄ μ`. -/
theorem hsConj_rankOne_eigen {c d : ℂ} {x y : H} (hx : x ∈ unitaryEigenspace U c)
    (hy : y ∈ unitaryEigenspace U d) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
    hsConj U (InnerProductSpace.rankOne ℂ x y) =
      ((starRingEnd ℂ) c * d) • InnerProductSpace.rankOne ℂ x y := by
  have hinner : ∀ v, ⟪y, U v⟫_ℂ = d * ⟪y, v⟫_ℂ := by
    intro v
    have : ⟪y, U v⟫_ℂ = ⟪U.symm y, v⟫_ℂ := by
      rw [← U.inner_map_map (U.symm y) v, U.apply_symm_apply]
    rw [this, unitary_symm_apply_of_mem hy hd, inner_smul_left, Complex.conj_conj]
  ext v
  simp only [hsConj_apply, InnerProductSpace.rankOne_apply, smul_apply, map_smul, hinner,
    unitary_symm_apply_of_mem hx hc, smul_smul]
  congr 1
  ring

end RankOne

/-! ### Column inner products and the fixed space -/

section ColumnInner

variable {ι : Type*} (b : HilbertBasis ι ℂ H) {U : H ≃ₗᵢ[ℂ] H}

theorem hsColumns_add_smul {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B)
    (r : ℂ) : hsColumns b hA + r • hsColumns b hB = hsColumns b (hA.add (hB.smul r)) :=
  lp.ext (funext fun j => by simp [hsColumns_apply])

/-- **The column inner product does not depend on the Hilbert basis.**  By polarization it is a
combination of Hilbert–Schmidt norms. -/
theorem inner_hsColumns_eq {κ : Type*} (b' : HilbertBasis κ ℂ H) {A B : H →L[ℂ] H}
    (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    ⟪hsColumns b hA, hsColumns b hB⟫_ℂ = ⟪hsColumns b' hA, hsColumns b' hB⟫_ℂ := by
  have key : ∀ r : ℂ, ‖hsColumns b hA + r • hsColumns b hB‖ =
      ‖hsColumns b' hA + r • hsColumns b' hB‖ := fun r => by
    rw [hsColumns_add_smul, hsColumns_add_smul, norm_hsColumns, norm_hsColumns]
  have h1 : ‖hsColumns b hA + hsColumns b hB‖ = ‖hsColumns b' hA + hsColumns b' hB‖ := by
    simpa using key 1
  have h2 : ‖hsColumns b hA - hsColumns b hB‖ = ‖hsColumns b' hA - hsColumns b' hB‖ := by
    simpa [sub_eq_add_neg] using key (-1)
  have h3 : ‖hsColumns b hA - (RCLike.I : ℂ) • hsColumns b hB‖ =
      ‖hsColumns b' hA - (RCLike.I : ℂ) • hsColumns b' hB‖ := by
    simpa [sub_eq_add_neg] using key (-Complex.I)
  have h4 : ‖hsColumns b hA + (RCLike.I : ℂ) • hsColumns b hB‖ =
      ‖hsColumns b' hA + (RCLike.I : ℂ) • hsColumns b' hB‖ := by
    simpa using key Complex.I
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ), inner_eq_sum_norm_sq_div_four (𝕜 := ℂ), h1, h2, h3,
    h4]

/-- Against a fixed operator, the column inner product only sees the atomic pinching. -/
theorem inner_hsColumns_fixed {F R : H →L[ℂ] H} (hF : IsHilbertSchmidt F)
    (hfix : hsConj U F = F) (hR : IsHilbertSchmidt R) :
    ⟪hsColumns b hF, hsColumns b hR⟫_ℂ =
      ⟪hsColumns b hF, hsColumns b (isHilbertSchmidt_atomicPinch (U := U) hR)⟫_ℂ := by
  rw [inner_hsColumns_eq b (adaptedBasis U), inner_hsColumns_eq b (adaptedBasis U),
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun j => ?_
  simp only [hsColumns_apply, adaptedBasis_apply]
  have h := inner_sub_atomicPinch_fixed (U := U) hR hF hfix j
  rw [sub_apply, inner_sub_left, sub_eq_zero] at h
  rw [← inner_conj_symm, h, inner_conj_symm]

theorem hsColumns_eq_zero {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (h : T = 0) :
    hsColumns b hT = 0 :=
  lp.ext (funext fun j => by simp [hsColumns_apply, h])

theorem columnOperator_zero : columnOperator b (0 : lp (fun _ : ι => H) 2) = 0 := by
  simpa using columnOperator_smul b 0 0

/-- The fixed columns are the columns of fixed operators. -/
theorem hsConj_columnOperator_of_fixed {x : lp (fun _ : ι => H) 2} (hx : columnConj b U x = x) :
    hsConj U (columnOperator b x) = columnOperator b x := by
  have h := congrArg (columnOperator b) hx
  rwa [show columnConj b U x = hsColumns b
      (isHilbertSchmidt_hsConj (U := U) (isHilbertSchmidt_columnOperator b x)) from rfl,
    columnOperator_hsColumns] at h

/-- The kernel of the column transgression `α - 1`. -/
abbrev transgressionKer (U : H ≃ₗᵢ[ℂ] H) : Submodule ℂ (lp (fun _ : ι => H) 2) :=
  LinearMap.ker ((columnConj b U - 1 : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2) :
    lp (fun _ : ι => H) 2 →ₗ[ℂ] lp (fun _ : ι => H) 2)

theorem mem_transgressionKer {x : lp (fun _ : ι => H) 2} :
    x ∈ transgressionKer b U ↔ columnConj b U x = x := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply, one_apply_eq_self, sub_eq_zero]

theorem columnTransgression_hsColumns {X : H →L[ℂ] H} (hX : IsHilbertSchmidt X) :
    (columnConj b U - 1 : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2) (hsColumns b hX) =
      hsColumns b ((isHilbertSchmidt_hsConj (U := U) hX).sub hX) := by
  rw [sub_apply, one_apply_eq_self, columnConj_hsColumns]
  rfl

/-- Vanishing atomic pinching puts the columns orthogonal to the fixed space. -/
theorem hsColumns_mem_ker_orthogonal {R : H →L[ℂ] H} (hR : IsHilbertSchmidt R)
    (hpin : atomicPinch U hR = 0) : hsColumns b hR ∈ (transgressionKer b U)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro k hk
  have hfix := hsConj_columnOperator_of_fixed b ((mem_transgressionKer b).mp hk)
  have h := inner_hsColumns_fixed b (isHilbertSchmidt_columnOperator b k) hfix hR
  rw [hsColumns_columnOperator, hsColumns_eq_zero b _ hpin, inner_zero_right] at h
  exact h

/-- Columns orthogonal to the fixed space have vanishing atomic pinching. -/
theorem atomicPinch_columnOperator_eq_zero {x : lp (fun _ : ι => H) 2}
    (hx : x ∈ (transgressionKer b U)ᗮ) :
    atomicPinch U (isHilbertSchmidt_columnOperator b x) = 0 := by
  have hX := isHilbertSchmidt_columnOperator b x
  have hP := isHilbertSchmidt_atomicPinch (U := U) hX
  have hmem : hsColumns b hP ∈ transgressionKer b U := by
    rw [mem_transgressionKer, columnConj_hsColumns]
    exact lp.ext (funext fun j => by simp only [hsColumns_apply, hsConj_atomicPinch hX])
  have h0 : ⟪hsColumns b hP, hsColumns b hX⟫_ℂ = 0 := by
    rw [hsColumns_columnOperator]
    exact (Submodule.mem_orthogonal _ _).mp hx _ hmem
  rw [inner_hsColumns_fixed b hP (hsConj_atomicPinch hX) hX, inner_self_eq_zero] at h0
  rw [← columnOperator_hsColumns b hP, h0, columnOperator_zero]

/-- **Closed range is a transverse lower bound** on the operators with vanishing atomic
pinching. -/
theorem isClosed_range_columnTransgression_iff :
    IsClosed (Set.range
      (columnConj b U - 1 : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2)) ↔
      ∃ c > 0, ∀ X : H →L[ℂ] H, ∀ hX : IsHilbertSchmidt X, atomicPinch U hX = 0 →
        c * X.hsNorm ≤ (hsConj U X - X).hsNorm := by
  rw [← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range]
  constructor
  · rintro ⟨c, hc, hlow⟩
    refine ⟨c, hc, fun X hX hpin => ?_⟩
    have h := hlow (hsColumns b hX) (hsColumns_mem_ker_orthogonal b hX hpin)
    rwa [columnTransgression_hsColumns, norm_hsColumns, norm_hsColumns] at h
  · rintro ⟨c, hc, hbd⟩
    refine ⟨c, hc, fun x hx => ?_⟩
    have h := hbd _ (isHilbertSchmidt_columnOperator b x) (atomicPinch_columnOperator_eq_zero b hx)
    have e2 : ‖(columnConj b U - 1 : lp (fun _ : ι => H) 2 →L[ℂ] _) x‖ =
        (hsConj U (columnOperator b x) - columnOperator b x).hsNorm := by
      conv_lhs => rw [← hsColumns_columnOperator b x]
      rw [columnTransgression_hsColumns, norm_hsColumns]
    rw [← norm_columnOperator_hs b x, e2]
    exact h

end ColumnInner

/-! ### Finite eigen-block decompositions -/

section Blocks

variable {U : H ≃ₗᵢ[ℂ] H}

theorem apertureProj_apply (s : Finset ℂ) (y : H) :
    apertureProj U s y = ∑ c ∈ s, eigenproj U c y := by
  rw [apertureProj, sum_apply]

omit [CompleteSpace H] in
theorem orthogonalFamily_unitaryEigenspace :
    OrthogonalFamily ℂ (fun c => unitaryEigenspace U c)
      fun c => (unitaryEigenspace U c).subtypeₗᵢ :=
  orthogonalFamily_iff_pairwise.mpr fun _ _ hcd => unitaryEigenspace_isOrtho hcd

/-- **Pythagoras over eigen-blocks.**  `‖∑_λ a_λ P_λ y‖² = ∑_λ |a_λ|² ‖P_λ y‖²`. -/
theorem norm_sum_eigenproj_sq (s : Finset ℂ) (a : ℂ → ℂ) (y : H) :
    ‖∑ c ∈ s, a c • eigenproj U c y‖ ^ 2 = ∑ c ∈ s, ‖a c‖ ^ 2 * ‖eigenproj U c y‖ ^ 2 := by
  have h := (orthogonalFamily_unitaryEigenspace (U := U)).norm_sum
    (fun c => (⟨a c • eigenproj U c y, Submodule.smul_mem _ _
      (Submodule.starProjection_apply_mem _ y)⟩ : unitaryEigenspace U c)) s
  simpa [norm_smul, mul_pow] using h

theorem norm_sq_eq_sum_eigenproj {s : Finset ℂ} {y : H} (hy : apertureProj U s y = y) :
    ‖y‖ ^ 2 = ∑ c ∈ s, ‖eigenproj U c y‖ ^ 2 := by
  have h := norm_sum_eigenproj_sq (U := U) s (fun _ => 1) y
  simp only [one_smul, norm_one, one_pow, one_mul] at h
  rw [← h, ← apertureProj_apply, hy]

/-- **Lower bound over eigen-blocks.**  If every occupied block multiplier has modulus at least
`c`, then `c ‖y‖ ≤ ‖∑_λ a_λ P_λ y‖`. -/
theorem le_norm_sum_eigenproj {s : Finset ℂ} (a : ℂ → ℂ) {y : H} (hy : apertureProj U s y = y)
    {c : ℝ} (hc : 0 ≤ c) (ha : ∀ d ∈ s, eigenproj U d y ≠ 0 → c ≤ ‖a d‖) :
    c * ‖y‖ ≤ ‖∑ d ∈ s, a d • eigenproj U d y‖ := by
  have hsq : (c * ‖y‖) ^ 2 ≤ ‖∑ d ∈ s, a d • eigenproj U d y‖ ^ 2 := by
    rw [norm_sum_eigenproj_sq, mul_pow, norm_sq_eq_sum_eigenproj hy, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    by_cases h : eigenproj U d y = 0
    · simp [h]
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc (ha d hd h) 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq

theorem exists_pos_le_of_finset {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ S, 0 < f a) : ∃ ε > 0, ∀ a ∈ S, ε ≤ f a := by
  by_cases hS : S.Nonempty
  · exact ⟨S.inf' hS f, (Finset.lt_inf'_iff hS).mpr hf, fun a ha => Finset.inf'_le f ha⟩
  · exact ⟨1, one_pos, fun a ha => absurd ⟨a, ha⟩ hS⟩

/-- A finite set of complex numbers has a positive minimal gap. -/
theorem exists_separation_of_finset (s : Finset ℂ) : ∃ c > 0, ∀ d ∈ s, ∀ e ∈ s, d ≠ e → c ≤ ‖d - e‖ := by
  classical
  obtain ⟨c, hc, hle⟩ := exists_pos_le_of_finset s.offDiag (fun p => ‖p.1 - p.2‖)
    fun p hp => norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_offDiag.mp hp).2.2)
  exact ⟨c, hc, fun d hd e he hde => hle (d, e) (Finset.mem_offDiag.mpr ⟨hd, he, hde⟩)⟩

omit [CompleteSpace H] in
theorem exists_unit_mem {K : Submodule ℂ H} (hK : K ≠ ⊥) : ∃ x ∈ K, ‖x‖ = 1 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  refine ⟨(‖x‖ : ℂ)⁻¹ • x, K.smul_mem _ hx, ?_⟩
  rw [norm_smul, norm_inv, Complex.norm_real, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]

theorem mem_pointSpectrum_of_adaptedVec (d : ℂ) (k : eigenBasisIndex U d) :
    d ∈ unitaryPointSpectrum U := by
  have hne : adaptedVec U (Sum.inl ⟨d, k⟩) ≠ 0 := by
    intro h0
    have := (orthonormal_adaptedVec (U := U)).1 (Sum.inl ⟨d, k⟩)
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact fun hbot => hne ((Submodule.eq_bot_iff _).mp hbot _ (adaptedVec_inl_mem d k))

theorem isEmpty_continuousBasisIndex (hc : continuousSubspace U = ⊥) :
    IsEmpty (continuousBasisIndex U) := by
  refine ⟨fun k => ?_⟩
  have hmem : adaptedVec U (Sum.inr k) = 0 :=
    (Submodule.eq_bot_iff _).mp hc _ (adaptedVec_inr_mem (U := U) k)
  have := (orthonormal_adaptedVec (U := U)).1 (Sum.inr k)
  rw [hmem, norm_zero] at this
  exact zero_ne_one this

/-- With no continuous part, an aperture containing every eigenvalue is the identity. -/
theorem apertureProj_eq_one {s : Finset ℂ} (hs : ∀ d ∈ unitaryPointSpectrum U, d ∈ s)
    (hc : continuousSubspace U = ⊥) : apertureProj U s = 1 := by
  refine ext_adapted (U := U) fun i => ?_
  rcases i with ⟨d, k⟩ | k
  · rw [apertureProj_adaptedVec_inl, if_pos (hs d (mem_pointSpectrum_of_adaptedVec d k)),
      one_apply_eq_self]
  · exact (isEmpty_continuousBasisIndex hc).elim k

end Blocks

/-! ### Finite spectrum -/

section FiniteSpectrum

variable {U : H ≃ₗᵢ[ℂ] H}

theorem isStarNormal_unitaryCLM (U : H ≃ₗᵢ[ℂ] H) : IsStarNormal (unitaryCLM U) := by
  refine ⟨?_⟩
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_unitaryCLM]
  show unitaryCLM U.symm * unitaryCLM U = unitaryCLM U * unitaryCLM U.symm
  ext x
  simp [mul_apply_eq_comp]

/-- **A finite spectrum leaves no continuous part.**  The spectral indicators
`e_λ = 1_{λ}(U)` of the continuous functional calculus sum to the identity and satisfy
`U e_λ = λ e_λ`, so every vector is a finite sum of eigenvectors. -/
theorem continuousSubspace_eq_bot_of_finite (hσ : (spectrum ℂ (unitaryCLM U)).Finite) :
    continuousSubspace U = ⊥ := by
  classical
  haveI := isStarNormal_unitaryCLM U
  set f : ℂ → ℂ → ℂ := fun c w => if w = c then 1 else 0
  have hcont : ∀ g : ℂ → ℂ, ContinuousOn g (spectrum ℂ (unitaryCLM U)) := by
    intro g
    rw [continuousOn_iff_continuous_restrict]
    haveI : Finite (spectrum ℂ (unitaryCLM U)) := hσ.to_subtype
    exact continuous_of_discreteTopology
  set e : ℂ → H →L[ℂ] H := fun c => cfc (f c) (unitaryCLM U)
  have hsum : ∑ c ∈ hσ.toFinset, e c = 1 := by
    rw [← cfc_sum f (unitaryCLM U) hσ.toFinset (fun c _ => hcont _), ← cfc_one ℂ (unitaryCLM U)]
    refine cfc_congr fun w hw => ?_
    rw [Finset.sum_apply, Pi.one_apply]
    simp only [f]
    rw [Finset.sum_ite_eq hσ.toFinset w (fun _ => (1 : ℂ)), if_pos (hσ.mem_toFinset.mpr hw)]
  have heig : ∀ c, unitaryCLM U * e c = c • e c := by
    intro c
    calc unitaryCLM U * e c = cfc id (unitaryCLM U) * cfc (f c) (unitaryCLM U) := by
          rw [cfc_id ℂ (unitaryCLM U)]
      _ = cfc (fun x => id x * f c x) (unitaryCLM U) :=
          (cfc_mul id (f c) _ (hcont _) (hcont _)).symm
      _ = cfc (fun x => c • f c x) (unitaryCLM U) :=
          cfc_congr fun w _ => by by_cases h : w = c <;> simp [f, h]
      _ = c • e c := cfc_smul c (f c) _ (hcont _)
  have hat : atomicSubspace U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ c ∈ hσ.toFinset, e c x := by
      rw [← sum_apply, hsum, one_apply_eq_self]
    rw [hx]
    refine Submodule.sum_mem _ fun c _ => unitaryEigenspace_le_atomic c ?_
    rw [mem_unitaryEigenspace]
    have := congrArg (fun L : H →L[ℂ] H => L x) (heig c)
    simpa [mul_apply_eq_comp] using this
  rw [continuousSubspace, hat, Submodule.top_orthogonal_eq_bot]

/-- Without continuous part and with finitely many eigenvalues, every spectral value is an
eigenvalue: off the eigenvalues `z - U` is bounded below by the distance to them. -/
theorem spectrum_subset_pointSpectrum (hA : (unitaryPointSpectrum U).Finite)
    (hc : continuousSubspace U = ⊥) :
    spectrum ℂ (unitaryCLM U) ⊆ unitaryPointSpectrum U := by
  intro z hz
  by_contra hzA
  obtain ⟨ε, hε, hεle⟩ := exists_pos_le_of_finset hA.toFinset (fun d => ‖d - z‖)
    fun d hd => norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hzA (h ▸ hA.mem_toFinset.mp hd))
  refine not_mem_spectrum_of_boundedBelow hε (fun y => ?_) hz
  have hQ := apertureProj_eq_one (U := U) (s := hA.toFinset) (fun d hd => hA.mem_toFinset.mpr hd)
    hc
  have hy : apertureProj U hA.toFinset y = y := by rw [hQ, one_apply_eq_self]
  have hexp : z • y - U y = ∑ d ∈ hA.toFinset, (z - d) • eigenproj U d y := by
    conv_lhs => rw [← hy, apertureProj_apply]
    rw [Finset.smul_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [mem_unitaryEigenspace.mp (Submodule.starProjection_apply_mem _ y), sub_smul]
  rw [hexp]
  refine le_norm_sum_eigenproj _ hy hε.le fun d hd _ => ?_
  rw [norm_sub_rev]
  exact hεle d hd

/-- **The spectrum is finite exactly when there are finitely many eigenvalues and no continuous
part.** -/
theorem spectrum_finite_iff :
    (spectrum ℂ (unitaryCLM U)).Finite ↔
      (unitaryPointSpectrum U).Finite ∧ continuousSubspace U = ⊥ :=
  ⟨fun hσ => ⟨hσ.subset fun _ hc => mem_spectrum_of_mem_pointSpectrum hc,
      continuousSubspace_eq_bot_of_finite hσ⟩,
    fun ⟨hA, hc⟩ => hA.subset (spectrum_subset_pointSpectrum hA hc)⟩

end FiniteSpectrum

/-! ### The transverse lower bound -/

section LowerBound

variable {U : H ≃ₗᵢ[ℂ] H}

omit [CompleteSpace H] in
theorem transgression_apply_eigen {μ : ℂ} {v : H} (hv : v ∈ unitaryEigenspace U μ)
    (X : H →L[ℂ] H) : (hsConj U X - X) v = μ • U.symm (X v) - X v := by
  rw [sub_apply, hsConj_apply, mem_unitaryEigenspace.mp hv, map_smul, map_smul]

/-- `U*` on a vector supported in a finite aperture acts blockwise by `λ̄`. -/
theorem symm_eq_sum_eigenproj {s : Finset ℂ} {y : H} (hy : apertureProj U s y = y) :
    U.symm y = ∑ d ∈ s, (starRingEnd ℂ) d • eigenproj U d y := by
  conv_lhs => rw [← hy, apertureProj_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h0 : eigenproj U d y = 0
  · rw [h0, map_zero, smul_zero]
  · exact unitary_symm_apply_of_mem (Submodule.starProjection_apply_mem _ y)
      (norm_eq_one_of_mem_unitaryEigenspace (Submodule.starProjection_apply_mem _ y) h0)

theorem norm_mul_conj_sub_one {μ d : ℂ} (hd : ‖d‖ = 1) :
    ‖μ * (starRingEnd ℂ) d - 1‖ = ‖μ - d‖ := by
  have : (μ * (starRingEnd ℂ) d - 1) * d = μ - d := by
    rw [sub_mul, mul_assoc, Complex.conj_mul', hd]
    simp
  rw [← this, norm_mul, hd, mul_one]

/-- **Column lower bound on a finite aperture.**  If `X` is supported in the aperture `s` and has
vanishing atomic pinching, every column satisfies `c ‖X v‖ ≤ ‖δ(X) v‖` for any `c` below the gaps
between distinct eigenvalues in `s`. -/
theorem aperture_column_lowerBound {s : Finset ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hgap : ∀ d ∈ s, ∀ e ∈ s, d ∈ unitaryPointSpectrum U → e ∈ unitaryPointSpectrum U → d ≠ e →
      c ≤ ‖d - e‖)
    {X : H →L[ℂ] H} (hX : IsHilbertSchmidt X) (hpin : atomicPinch U hX = 0)
    (hXQ : X ∘L apertureProj U s = X) (hQX : apertureProj U s ∘L X = X) (j : AdaptedIndex U) :
    c * ‖X (adaptedVec U j)‖ ≤ ‖(hsConj U X - X) (adaptedVec U j)‖ := by
  have hXv : ∀ v, apertureProj U s v = 0 → X v = 0 := fun v hv => by
    rw [← hXQ, ContinuousLinearMap.comp_apply, hv, map_zero]
  rcases j with ⟨μ, k⟩ | k
  · by_cases hμ : μ ∈ s
    · have hv := adaptedVec_inl_mem (U := U) μ k
      have hμA := mem_pointSpectrum_of_adaptedVec (U := U) μ k
      have hy : apertureProj U s (X (adaptedVec U (Sum.inl ⟨μ, k⟩))) =
          X (adaptedVec U (Sum.inl ⟨μ, k⟩)) := DFunLike.congr_fun hQX _
      have hPμ : eigenproj U μ (X (adaptedVec U (Sum.inl ⟨μ, k⟩))) = 0 := by
        have h := atomicPinch_apply (U := U) hX (Sum.inl ⟨μ, k⟩)
        rw [hpin, zero_apply] at h
        exact h.symm
      have hsum : X (adaptedVec U (Sum.inl ⟨μ, k⟩)) =
          ∑ d ∈ s, eigenproj U d (X (adaptedVec U (Sum.inl ⟨μ, k⟩))) := by
        rw [← apertureProj_apply, hy]
      have hexp : (hsConj U X - X) (adaptedVec U (Sum.inl ⟨μ, k⟩)) =
          ∑ d ∈ s, (μ * (starRingEnd ℂ) d - 1) •
            eigenproj U d (X (adaptedVec U (Sum.inl ⟨μ, k⟩))) := by
        rw [transgression_apply_eigen hv, symm_eq_sum_eigenproj hy, Finset.smul_sum]
        conv_lhs => arg 2; rw [hsum]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [smul_smul, sub_smul, one_smul]
      rw [hexp]
      refine le_norm_sum_eigenproj _ hy hc fun d hd hPd => ?_
      have hdA : d ∈ unitaryPointSpectrum U := fun hbot =>
        hPd ((Submodule.eq_bot_iff _).mp hbot _ (Submodule.starProjection_apply_mem _ _))
      have hdμ : d ≠ μ := fun h => hPd (h ▸ hPμ)
      rw [norm_mul_conj_sub_one (norm_eq_one_of_mem_pointSpectrum hdA), norm_sub_rev]
      exact hgap d hd μ hμ hdA hμA hdμ
    · have hv0 : apertureProj U s (adaptedVec U (Sum.inl ⟨μ, k⟩)) = 0 := by
        rw [apertureProj_adaptedVec_inl, if_neg hμ]
      rw [hXv _ hv0, norm_zero, mul_zero]
      exact norm_nonneg _
  · rw [hXv _ (apertureProj_adaptedVec_inr s k), norm_zero, mul_zero]
    exact norm_nonneg _

/-- Columnwise lower bounds on the adapted basis give the Hilbert–Schmidt lower bound. -/
theorem hsNorm_lowerBound_of_columns {c : ℝ} (hc : 0 ≤ c) {X : H →L[ℂ] H}
    (hX : IsHilbertSchmidt X)
    (hcol : ∀ j, c * ‖X (adaptedVec U j)‖ ≤ ‖(hsConj U X - X) (adaptedVec U j)‖) :
    c * X.hsNorm ≤ (hsConj U X - X).hsNorm := by
  have hD : IsHilbertSchmidt (hsConj U X - X) := (isHilbertSchmidt_hsConj hX).sub hX
  rw [ContinuousLinearMap.hsNorm, ContinuousLinearMap.hsNorm, ← Real.sqrt_sq hc,
    ← Real.sqrt_mul (sq_nonneg c)]
  refine Real.sqrt_le_sqrt ?_
  rw [hsNormSq_eq hX (adaptedBasis U), hsNormSq_eq hD (adaptedBasis U), ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun j => ?_) ((hX.summable _).mul_left _) (hD.summable _)
  rw [adaptedBasis_apply, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (hcol j) 2

/-- **Finite apertures have bounded inverses** on their off-resonant blocks: `c ‖X‖₂ ≤ ‖δ X‖₂`
for `X` supported in the aperture with vanishing atomic pinching. -/
theorem aperture_lowerBound {s : Finset ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hgap : ∀ d ∈ s, ∀ e ∈ s, d ∈ unitaryPointSpectrum U → e ∈ unitaryPointSpectrum U → d ≠ e →
      c ≤ ‖d - e‖)
    {X : H →L[ℂ] H} (hX : IsHilbertSchmidt X) (hpin : atomicPinch U hX = 0)
    (hXQ : X ∘L apertureProj U s = X) (hQX : apertureProj U s ∘L X = X) :
    c * X.hsNorm ≤ (hsConj U X - X).hsNorm :=
  hsNorm_lowerBound_of_columns hc hX (aperture_column_lowerBound hc hgap hX hpin hXQ hQX)

/-- **Corollary 6.2, finite apertures.**  Every finite eigenvalue aperture carries a positive
lower bound for the transgression on its off-resonant blocks. -/
theorem exists_apertureInverse (U : H ≃ₗᵢ[ℂ] H) (s : Finset ℂ) :
    ∃ c > 0, ∀ X : H →L[ℂ] H, ∀ hX : IsHilbertSchmidt X, atomicPinch U hX = 0 →
      X ∘L apertureProj U s = X → apertureProj U s ∘L X = X →
        c * X.hsNorm ≤ (hsConj U X - X).hsNorm := by
  obtain ⟨c, hc, hgap⟩ := exists_separation_of_finset s
  exact ⟨c, hc, fun X hX hpin hXQ hQX =>
    aperture_lowerBound hc.le (fun d hd e he _ _ hde => hgap d hd e he hde) hX hpin hXQ hQX⟩

/-- Two eigenvectors of distinct eigenvalues give a rank-one operator with vanishing atomic
pinching. -/
theorem atomicPinch_rankOne_eigen {c d : ℂ} (hcd : c ≠ d) {x y : H}
    (hx : x ∈ unitaryEigenspace U c) (hy : y ∈ unitaryEigenspace U d) :
    atomicPinch U (isHilbertSchmidt_rankOne x y) = 0 := by
  refine ext_adapted (U := U) fun i => ?_
  rw [atomicPinch_apply, zero_apply]
  rcases i with ⟨e, k⟩ | k
  · show eigenproj U e (InnerProductSpace.rankOne ℂ x y (adaptedVec U (Sum.inl ⟨e, k⟩))) = 0
    rw [InnerProductSpace.rankOne_apply, map_smul]
    by_cases hec : e = c
    · subst hec
      rw [(unitaryEigenspace_isOrtho hcd.symm).inner_eq hy (adaptedVec_inl_mem e k), zero_smul]
    · have hx' : eigenproj U c x = x := Submodule.starProjection_eq_self_iff.mpr hx
      rw [← hx', eigenproj_eigenproj_of_ne (Ne.symm hec), smul_zero]
  · rfl

/-- A continuous vector gives a rank-one operator with vanishing atomic pinching. -/
theorem atomicPinch_rankOne_continuous {u : H} (hu : u ∈ continuousSubspace U) (y : H) :
    atomicPinch U (isHilbertSchmidt_rankOne u y) = 0 := by
  refine ext_adapted (U := U) fun i => ?_
  rw [atomicPinch_apply, zero_apply]
  rcases i with ⟨e, k⟩ | k
  · show eigenproj U e (InnerProductSpace.rankOne ℂ u y (adaptedVec U (Sum.inl ⟨e, k⟩))) = 0
    rw [InnerProductSpace.rankOne_apply, map_smul,
      (Submodule.starProjection_apply_eq_zero_iff _).mpr
        (Submodule.orthogonal_le (unitaryEigenspace_le_atomic e) hu), smul_zero]
  · rfl

/-- On unit eigenvectors `x ∈ H_λ`, `y ∈ H_μ`: `‖δ |x⟩⟨y|‖₂ = |λ - μ|`. -/
theorem hsNorm_transgression_rankOne_eigen {c d : ℂ} {x y : H} (hx : x ∈ unitaryEigenspace U c)
    (hy : y ∈ unitaryEigenspace U d) (hx1 : ‖x‖ = 1) (hy1 : ‖y‖ = 1) :
    (hsConj U (InnerProductSpace.rankOne ℂ x y) - InnerProductSpace.rankOne ℂ x y).hsNorm =
      ‖c - d‖ := by
  have hc : ‖c‖ = 1 := norm_eq_one_of_mem_unitaryEigenspace hx (norm_ne_zero_iff.mp (by
    rw [hx1]; exact one_ne_zero))
  have hd : ‖d‖ = 1 := norm_eq_one_of_mem_unitaryEigenspace hy (norm_ne_zero_iff.mp (by
    rw [hy1]; exact one_ne_zero))
  have heq : hsConj U (InnerProductSpace.rankOne ℂ x y) - InnerProductSpace.rankOne ℂ x y =
      InnerProductSpace.rankOne ℂ (((starRingEnd ℂ) c * d - 1) • x) y := by
    rw [hsConj_rankOne_eigen hx hy hc hd, map_smul]
    ext v
    simp [sub_smul]
  rw [heq, hsNorm_rankOne, norm_smul, hx1, hy1, mul_one, mul_one, mul_comm,
    norm_mul_conj_sub_one hc, norm_sub_rev]

/-- **Spectral richness gives almost fixed rank-one operators orthogonal to the fixed space.**
Infinitely many eigenvalues give `|x⟩⟨y|` on two close eigenvalues; a nonzero continuous part
gives `|u⟩⟨u|` on an approximate eigenvector. -/
theorem exists_almostFixed_rankOne
    (h : ¬ ((unitaryPointSpectrum U).Finite ∧ continuousSubspace U = ⊥)) {c : ℝ} (hc : 0 < c) :
    ∃ x y : H, ∃ hX : IsHilbertSchmidt (InnerProductSpace.rankOne ℂ x y),
      atomicPinch U hX = 0 ∧ (InnerProductSpace.rankOne ℂ x y).hsNorm = 1 ∧
      (hsConj U (InnerProductSpace.rankOne ℂ x y) -
        InnerProductSpace.rankOne ℂ x y).hsNorm < c := by
  by_cases hA : (unitaryPointSpectrum U).Finite
  · have hc' : continuousSubspace U ≠ ⊥ := fun h' => h ⟨hA, h'⟩
    haveI : Nontrivial (continuousSubspace U) := Submodule.nontrivial_iff_ne_bot.mpr hc'
    obtain ⟨u, w, hu, hw, hclose⟩ :=
      hasApproxEigenvectors_of_nontrivial (continuousRestrict U) (c / 4) (by positivity)
    have hu' : ‖(u : H)‖ = 1 := hu
    have hclose' : ‖U u - w • (u : H)‖ ≤ c / 4 := hclose
    refine ⟨u, u, isHilbertSchmidt_rankOne _ _, atomicPinch_rankOne_continuous u.2 _, ?_, ?_⟩
    · rw [hsNorm_rankOne, hu', one_mul]
    · have := hsNorm_transgression_rankOne_le hu' hw hclose'
      linarith
  · obtain ⟨d, hd, e, he, hde, hlt⟩ := exists_ne_norm_sub_lt_of_infinite hA
      (fun w hw => norm_eq_one_of_mem_pointSpectrum hw) hc
    obtain ⟨x, hx, hx1⟩ := exists_unit_mem hd
    obtain ⟨y, hy, hy1⟩ := exists_unit_mem he
    refine ⟨x, y, isHilbertSchmidt_rankOne _ _, atomicPinch_rankOne_eigen hde hx hy, ?_, ?_⟩
    · rw [hsNorm_rankOne, hx1, hy1, one_mul]
    · rw [hsNorm_transgression_rankOne_eigen hx hy hx1 hy1]
      exact hlt

/-- **The transverse lower bound holds exactly for finitely many eigenvalues and no continuous
part.** -/
theorem exists_lowerBound_iff :
    (∃ c > 0, ∀ X : H →L[ℂ] H, ∀ hX : IsHilbertSchmidt X, atomicPinch U hX = 0 →
        c * X.hsNorm ≤ (hsConj U X - X).hsNorm) ↔
      (unitaryPointSpectrum U).Finite ∧ continuousSubspace U = ⊥ := by
  constructor
  · rintro ⟨c, hc, hbd⟩
    by_contra h
    obtain ⟨x, y, hX, hpin, h1, hlt⟩ := exists_almostFixed_rankOne h hc
    have := hbd _ hX hpin
    rw [h1, mul_one] at this
    linarith
  · rintro ⟨hA, hcb⟩
    obtain ⟨c, hc, hgap⟩ := exists_separation_of_finset hA.toFinset
    have hQ := apertureProj_eq_one (U := U) (s := hA.toFinset)
      (fun d hd => hA.mem_toFinset.mpr hd) hcb
    refine ⟨c, hc, fun X hX hpin => aperture_lowerBound hc.le
      (fun d hd e he _ _ hde => hgap d hd e he hde) hX hpin ?_ ?_⟩
    · rw [hQ]
      ext v
      simp
    · rw [hQ]
      ext v
      simp

end LowerBound

/-! ### The closed-range law -/

section ClosedRange

variable {ι : Type*} (b : HilbertBasis ι ℂ H) (U : H ≃ₗᵢ[ℂ] H)

/-- **Theorem 6.1, `(MSF.11)`.**  The transgression `1 - Ad_U` on the Hilbert–Schmidt ideal has
closed range exactly when the spectrum of `U` is finite. -/
theorem isClosed_range_columnTransgression_iff_finite_spectrum :
    IsClosed (Set.range
      (columnConj b U - 1 : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2)) ↔
      (spectrum ℂ (unitaryCLM U)).Finite := by
  rw [isClosed_range_columnTransgression_iff, exists_lowerBound_iff, spectrum_finite_iff]

/-- **Corollary 6.2, global ill-conditioning.**  The spectrum of `U` is infinite exactly when, for
every `c > 0`, some rank-one Hilbert–Schmidt operator of norm one, orthogonal to the fixed space,
is moved by less than `c`.  No spectral type enters: pure point, singular continuous, absolutely
continuous and mixed spectra behave alike. -/
theorem spectrum_infinite_iff_almostFixed :
    (spectrum ℂ (unitaryCLM U)).Infinite ↔
      ∀ c > 0, ∃ x y : H, ∃ hX : IsHilbertSchmidt (InnerProductSpace.rankOne ℂ x y),
        atomicPinch U hX = 0 ∧ (InnerProductSpace.rankOne ℂ x y).hsNorm = 1 ∧
        (hsConj U (InnerProductSpace.rankOne ℂ x y) -
          InnerProductSpace.rankOne ℂ x y).hsNorm < c := by
  constructor
  · intro hinf c hc
    exact exists_almostFixed_rankOne (fun h => hinf (spectrum_finite_iff.mpr h)) hc
  · intro h hfin
    obtain ⟨c, hc, hbd⟩ := exists_lowerBound_iff.mpr (spectrum_finite_iff.mp hfin)
    obtain ⟨x, y, hX, hpin, h1, hlt⟩ := h c hc
    have := hbd _ hX hpin
    rw [h1, mul_one] at this
    linarith

/-- **Corollary 6.2, divergence along eigenvalue apertures.**  With infinitely many eigenvalues,
for every `c > 0` there is a finite aperture `s₀` such that every larger aperture carries a
norm-one off-resonant rank-one operator moved by less than `c`: the best inverse norms over
increasing apertures diverge. -/
theorem aperture_inverse_diverges (hA : (unitaryPointSpectrum U).Infinite) {c : ℝ} (hc : 0 < c) :
    ∃ s₀ : Finset ℂ, ∀ s : Finset ℂ, s₀ ⊆ s →
      ∃ x y : H, ∃ hX : IsHilbertSchmidt (InnerProductSpace.rankOne ℂ x y),
        atomicPinch U hX = 0 ∧
        InnerProductSpace.rankOne ℂ x y ∘L apertureProj U s = InnerProductSpace.rankOne ℂ x y ∧
        apertureProj U s ∘L InnerProductSpace.rankOne ℂ x y = InnerProductSpace.rankOne ℂ x y ∧
        (InnerProductSpace.rankOne ℂ x y).hsNorm = 1 ∧
        (hsConj U (InnerProductSpace.rankOne ℂ x y) -
          InnerProductSpace.rankOne ℂ x y).hsNorm < c := by
  classical
  obtain ⟨d, hd, e, he, hde, hlt⟩ := exists_ne_norm_sub_lt_of_infinite hA
    (fun w hw => norm_eq_one_of_mem_pointSpectrum hw) hc
  obtain ⟨x, hx, hx1⟩ := exists_unit_mem hd
  obtain ⟨y, hy, hy1⟩ := exists_unit_mem he
  refine ⟨{d, e}, fun s hs => ⟨x, y, isHilbertSchmidt_rankOne _ _,
    atomicPinch_rankOne_eigen hde hx hy, ?_, ?_, ?_, ?_⟩⟩
  · have hQy : apertureProj U s y = y := by
      rw [← Submodule.starProjection_eq_self_iff.mpr hy, apertureProj_eigenproj,
        if_pos (hs (by simp))]
    ext v
    have hsym : ⟪y, apertureProj U s v⟫_ℂ = ⟪apertureProj U s y, v⟫_ℂ :=
      ((isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_apertureProj (U := U) s)) y v).symm
    rw [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply,
      InnerProductSpace.rankOne_apply, hsym, hQy]
  · have hQx : apertureProj U s x = x := by
      rw [← Submodule.starProjection_eq_self_iff.mpr hx, apertureProj_eigenproj,
        if_pos (hs (by simp))]
    ext v
    rw [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply, map_smul, hQx]
  · rw [hsNorm_rankOne, hx1, hy1, one_mul]
  · rw [hsNorm_transgression_rankOne_eigen hx hy hx1 hy1]
    exact hlt

end ClosedRange

/-! ### The spectral formation table -/

section FieldTable

variable {U : H ≃ₗᵢ[ℂ] H} {T : H →L[ℂ] H}

theorem contproj_eq_zero_of_bot (hc : continuousSubspace U = ⊥) : contproj U = 0 := by
  ext x
  exact (Submodule.eq_bot_iff _).mp hc _ (Submodule.starProjection_apply_mem _ x)

theorem continuousMass_eq_zero_of_bot (hc : continuousSubspace U = ⊥) (T : H →L[ℂ] H) :
    continuousMass U T = 0 := by
  rw [continuousMass, contproj_eq_zero_of_bot hc, ContinuousLinearMap.comp_zero,
    RHTower.opTrace_zero]

/-- **Pure point spectrum, finite or infinite: trace-norm formation.**  With no continuous part,
the formation of every positive trace-class packet converges to its atomic pinching in trace
norm. -/
theorem tendsto_traceNorm_of_continuousSubspace_eq_bot (hc : continuousSubspace U = ⊥)
    (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive) :
    Tendsto (fun N => RHTower.traceNorm H
      (hsCesaro U N T - atomicPinch U hT.one_isHilbertSchmidt)) atTop (𝓝 0) :=
  (tendsto_traceNorm_iff_continuousMass_eq_zero hT hpos).mpr (continuousMass_eq_zero_of_bot hc T)

/-- **Atomless spectrum: the formation limit is zero.** -/
theorem atomicPinch_eq_zero_of_hasNoEigenvectors (hU : HasNoEigenvectors U) {X : H →L[ℂ] H}
    (hX : IsHilbertSchmidt X) : atomicPinch U hX = 0 :=
  eq_zero_of_hsConj_eq hU (isHilbertSchmidt_atomicPinch hX) (hsConj_atomicPinch hX)

/-- **Atomless spectrum: the whole trace escapes**, `m_c(T) = tr T`. -/
theorem continuousMass_eq_opTrace_of_hasNoEigenvectors (hU : HasNoEigenvectors U)
    (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive) :
    continuousMass U T = opTrace T := by
  rw [continuousMass_eq_sub hT hpos, atomicPinch_eq_zero_of_hasNoEigenvectors hU,
    RHTower.opTrace_zero, sub_zero]

/-- **Atomless spectrum: no trace-norm formation for a nonzero positive packet.** -/
theorem not_tendsto_traceNorm_of_hasNoEigenvectors (hU : HasNoEigenvectors U)
    (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive) (hT0 : T ≠ 0) :
    ¬ Tendsto (fun N => RHTower.traceNorm H
      (hsCesaro U N T - atomicPinch U hT.one_isHilbertSchmidt)) atTop (𝓝 0) := by
  rw [tendsto_traceNorm_iff_continuousMass_eq_zero hT hpos,
    continuousMass_eq_opTrace_of_hasNoEigenvectors hU hT hpos]
  intro h0
  have h1 := RHTower.traceNorm_eq_re_opTrace_of_isPositive hT hpos
  rw [h0, Complex.zero_re] at h1
  exact hT0 ((RHTower.traceNorm_eq_zero_iff hT.one_summable_approxNumber).mp h1)

end FieldTable

end GaloisForLFunctions.HTGeometry
