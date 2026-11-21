import GaloisForLFunctions.HTGeometry.CoordinateInnerProductToolkit
import GaloisForLFunctions.HTGeometry.HermitianTraceNorm
import GaloisForLFunctions.RHTower.RiemannGaussian.EtaEnergyFiniteWindowInertia
import GaloisForLFunctions.HilbertMetric.QuantumInformation.Recovery.ChainSiteReadout

/-!
# Pure-reference readout by a scalar resolvent

A pure reference minus a conditional density has at most one positive
eigenvalue, by the rank bound on its positive index. When the states
differ, this eigenvalue is their trace distance and is the unique
positive solution of a shifted-resolvent equation. This extends the
site readout in Kanno and Soda (arXiv:2611.26368, Eq. 7.19) to an
arbitrary retained set of sites and gives its attained binary
measurement optimum.
-/

open Matrix
open scoped BigOperators ComplexOrder Matrix

namespace GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The density of a normalized pure reference vector. -/
def pureReferenceDensity (v : ι → ℂ) : Matrix ι ι ℂ := Matrix.vecMulVec v (star v)

/-- The difference used to discriminate a pure reference from a conditional state. -/
def pureReferenceGap (v : ι → ℂ) (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  pureReferenceDensity v - ρ

/-- Trace distance from the pure reference. -/
def pureReferenceDistance (v : ι → ℂ) (ρ : Matrix ι ι ℂ) : ℝ :=
  finiteMatrixNuclearNorm (pureReferenceGap v ρ) / 2

omit [DecidableEq ι] in
private theorem reference_multiply (v x : ι → ℂ) :
    pureReferenceDensity v *ᵥ x = cinner v x • v := by
  funext i
  simp only [pureReferenceDensity, Matrix.mulVec, Matrix.vecMulVec, Matrix.of_apply,
    dotProduct, Pi.star_apply, Complex.star_def, cinner, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq ι] in
private theorem inner_smul_right (v x : ι → ℂ) (c : ℂ) :
    cinner v (c • x) = c * cinner v x := by
  simp only [cinner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem shifted_isUnit {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) {t : ℝ} (ht : 0 < t) :
    IsUnit (ρ + (t : ℂ) • (1 : Matrix ι ι ℂ)) := by
  have hp : ((t : ℂ) • (1 : Matrix ι ι ℂ)).PosDef := by
    have he : ((t : ℂ) • (1 : Matrix ι ι ℂ)) = Matrix.diagonal (fun _ : ι => (t : ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.smul_apply, h]
    rw [he, Matrix.posDef_diagonal_iff]
    intro i
    exact_mod_cast ht
  exact (Matrix.PosDef.posSemidef_add hρ hp).isUnit

/-- A positive gap eigenvalue is exactly a root of the pure-reference
secular equation. The corresponding eigenvector is the shifted inverse
applied to the reference vector, up to scalar. -/
theorem pureReferenceGap_eigenvector_iff (v : ι → ℂ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (∃ x : ι → ℂ, x ≠ 0 ∧ pureReferenceGap v ρ *ᵥ x = (t : ℂ) • x) ↔
      cinner v ((ρ + (t : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ v) = 1 := by
  let M := ρ + (t : ℂ) • (1 : Matrix ι ι ℂ)
  let y := M⁻¹ *ᵥ v
  have hU : IsUnit M.det := by
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact shifted_isUnit hρ ht
  have hleft : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hU
  have hright : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hU
  have hshift (x : ι → ℂ) : M *ᵥ x = ρ *ᵥ x + (t : ℂ) • x := by
    simp only [M, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hy : M *ᵥ y = v := by
    rw [show y = M⁻¹ *ᵥ v from rfl, Matrix.mulVec_mulVec, hright, Matrix.one_mulVec]
  change (∃ x : ι → ℂ, x ≠ 0 ∧ pureReferenceGap v ρ *ᵥ x = (t : ℂ) • x) ↔ cinner v y = 1
  constructor
  · rintro ⟨x, hx, he⟩
    rw [pureReferenceGap, Matrix.sub_mulVec, reference_multiply] at he
    have hMe : M *ᵥ x = cinner v x • v := by
      rw [hshift, add_comm]
      exact (eq_add_of_sub_eq he).symm
    have hspan : x = cinner v x • y := by
      have h := congrArg (fun z : ι → ℂ => M⁻¹ *ᵥ z) hMe
      simpa only [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec, Matrix.mulVec_smul, y] using h
    have hk : cinner v x ≠ 0 := fun hz => hx (by simpa only [hz, zero_smul] using hspan)
    have h := congrArg (cinner v) hspan
    rw [inner_smul_right] at h
    exact mul_left_cancel₀ hk (h.symm.trans (mul_one _).symm)
  · intro h
    have hyn : y ≠ 0 := fun hz => by simp [hz, cinner] at h
    refine ⟨y, hyn, ?_⟩
    rw [pureReferenceGap, Matrix.sub_mulVec, reference_multiply, h, one_smul]
    rw [hshift] at hy
    rw [← hy, add_sub_cancel_left]

omit [DecidableEq ι] in
private theorem pureReferenceGap_hermitian (v : ι → ℂ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) : (pureReferenceGap v ρ).IsHermitian :=
  (Matrix.posSemidef_vecMulVec_self_star v).isHermitian.sub hρ.isHermitian

private theorem pureReferenceGap_trace (v : ι → ℂ) {ρ : Matrix ι ι ℂ}
    (hv : cnormSq v = 1) (htr : ρ.trace = 1) : (pureReferenceGap v ρ).trace = 0 := by
  have h : v ⬝ᵥ star v = cinner v v := by
    simp [dotProduct, cinner, mul_comm]
  rw [pureReferenceGap, Matrix.trace_sub, pureReferenceDensity, Matrix.trace_vecMulVec, h,
    cinner_self, hv, Complex.ofReal_one, htr, sub_self]

private theorem positive_index_le_one (v : ι → ℂ) {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    (Finset.univ.filter fun i => 0 < (pureReferenceGap_hermitian v hρ).eigenvalues i).card ≤ 1 :=
  (RiemannGaussian.HermitianInertia.posIndex_sub_le_rank
    (Matrix.posSemidef_vecMulVec_self_star v) hρ).trans (Matrix.rank_vecMulVec_le v (star v))

private theorem distance_eq_positive_eigenvalue (v : ι → ℂ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hv : cnormSq v = 1) (htr : ρ.trace = 1) {i : ι}
    (hi : 0 < (pureReferenceGap_hermitian v hρ).eigenvalues i) :
    pureReferenceDistance v ρ = (pureReferenceGap_hermitian v hρ).eigenvalues i := by
  let hD := pureReferenceGap_hermitian v hρ
  let eigen := hD.eigenvalues
  have hsum : ∑ j, eigen j = 0 := by
    rw [← trace_re_eq_sum_eigenvalues hD, pureReferenceGap_trace v hv htr, Complex.zero_re]
  have hj (j : ι) (hne : j ≠ i) : eigen j ≤ 0 := by
    refine le_of_not_gt fun hj => hne (Finset.card_le_one_iff.mp (positive_index_le_one v hρ) ?_ ?_)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have htotal : (∑ j, |eigen j|) + ∑ j, eigen j = 2 * eigen i := by
    rw [← Finset.sum_add_distrib, Finset.sum_eq_single i]
    · rw [abs_of_pos hi, two_mul]
    · intro j _ hne
      rw [abs_of_nonpos (hj j hne), neg_add_cancel]
    · exact fun h => (h (Finset.mem_univ _)).elim
  unfold pureReferenceDistance
  rw [finiteMatrixNuclearNorm_isHermitian hD]
  linarith only [htotal, hsum]

private theorem eigenvalue_exists_of_vec {D : Matrix ι ι ℂ} (hD : D.IsHermitian) (t : ℝ)
    (x : ι → ℂ) (hx : x ≠ 0) (he : D *ᵥ x = (t : ℂ) • x) :
    ∃ i, hD.eigenvalues i = t := by
  have hspec : (t : ℂ) ∈ spectrum ℂ D := by
    apply spectrum.mem_iff.mpr
    intro hu
    have hs : IsUnit ((t : ℂ) • (1 : Matrix ι ι ℂ) - D) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hu
    apply hx
    apply Matrix.mulVec_injective_of_isUnit hs
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, he, sub_self, Matrix.mulVec_zero]
  rw [hD.spectrum_eq_image_range] at hspec
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hspec
  exact ⟨i, Complex.ofReal_injective hi⟩

/-- Every positive value of the trace distance is characterized by the
scalar resolvent equation. This also excludes roots at all other positive shifts. -/
theorem pureReferenceDistance_eq_pos_iff_resolvent (v : ι → ℂ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hv : cnormSq v = 1) (htr : ρ.trace = 1) {t : ℝ} (ht : 0 < t) :
    pureReferenceDistance v ρ = t ↔
      cinner v ((ρ + (t : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ v) = 1 := by
  let hD := pureReferenceGap_hermitian v hρ
  constructor
  · intro he
    have hpos : ∃ i, 0 < hD.eigenvalues i := by
      by_contra! h
      have hsum : ∑ j, hD.eigenvalues j = 0 := by
        rw [← trace_re_eq_sum_eigenvalues hD, pureReferenceGap_trace v hv htr, Complex.zero_re]
      have hnorm : finiteMatrixNuclearNorm (pureReferenceGap v ρ) = 0 := by
        rw [finiteMatrixNuclearNorm_isHermitian hD]
        calc
          _ = ∑ j, -hD.eigenvalues j := Finset.sum_congr rfl fun j _ => abs_of_nonpos (h j)
          _ = 0 := by rw [Finset.sum_neg_distrib, hsum, neg_zero]
      unfold pureReferenceDistance at he
      linarith only [ht, hnorm, he]
    obtain ⟨i, hi⟩ := hpos
    have ht' : hD.eigenvalues i = t := (distance_eq_positive_eigenvalue v hρ hv htr hi).symm.trans he
    let x : ι → ℂ := ⇑(hD.eigenvectorBasis i)
    have hx : x ≠ 0 := by
      intro hz
      apply (hD.eigenvectorBasis.orthonormal.ne_zero i)
      ext j
      exact congrFun hz j
    refine (pureReferenceGap_eigenvector_iff v hρ ht).mp ⟨x, hx, ?_⟩
    have hm : pureReferenceGap v ρ *ᵥ x = hD.eigenvalues i • x := hD.mulVec_eigenvectorBasis i
    rw [ht'] at hm
    exact hm
  · intro h
    obtain ⟨x, hx, he⟩ := (pureReferenceGap_eigenvector_iff v hρ ht).mpr h
    obtain ⟨i, hi⟩ := eigenvalue_exists_of_vec hD t x hx he
    have hpos : 0 < hD.eigenvalues i := by rwa [hi]
    exact (distance_eq_positive_eigenvalue v hρ hv htr hpos).trans hi

/-- Distinct normalized states give exactly one positive root of the
resolvent equation. -/
theorem existsUnique_pureReference_resolvent_root (v : ι → ℂ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hv : cnormSq v = 1) (htr : ρ.trace = 1)
    (hne : pureReferenceDensity v ≠ ρ) :
    ∃! t : ℝ, 0 < t ∧ cinner v ((ρ + (t : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ v) = 1 := by
  have hgap : pureReferenceGap v ρ ≠ 0 := sub_ne_zero.mpr hne
  have hn : finiteMatrixNuclearNorm (pureReferenceGap v ρ) ≠ 0 :=
    fun h => hgap ((finiteMatrixNuclearNorm_eq_zero_iff _).mp h)
  have hd : 0 < pureReferenceDistance v ρ :=
    div_pos (lt_of_le_of_ne (finiteMatrixNuclearNorm_nonneg _) (Ne.symm hn)) (by norm_num)
  refine ⟨pureReferenceDistance v ρ, ⟨hd, (pureReferenceDistance_eq_pos_iff_resolvent v hρ hv htr hd).mp rfl⟩, ?_⟩
  intro t ht
  exact ((pureReferenceDistance_eq_pos_iff_resolvent v hρ hv htr ht.1).mpr ht.2).symm

/-- Equal states are exactly the case with no positive resolvent root. -/
theorem no_pureReference_resolvent_root_iff_eq (v : ι → ℂ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hv : cnormSq v = 1) (htr : ρ.trace = 1) :
    (¬∃ t : ℝ, 0 < t ∧ cinner v ((ρ + (t : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ v) = 1) ↔
      pureReferenceDensity v = ρ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨t, ht, _⟩ := existsUnique_pureReference_resolvent_root v hρ hv htr hne
    exact h ⟨t, ht⟩
  · rintro he ⟨t, ht, hr⟩
    have hd := (pureReferenceDistance_eq_pos_iff_resolvent v hρ hv htr ht).mpr hr
    have hgap : pureReferenceGap v ρ = 0 := sub_eq_zero.mpr he
    unfold pureReferenceDistance at hd
    rw [(finiteMatrixNuclearNorm_eq_zero_iff _).mpr hgap, zero_div] at hd
    exact ht.ne' hd.symm

/-- Partial trace of an embedded normalized amplitude gives a density matrix. -/
theorem sparseReduction_density {J L F : Type*} [Fintype J] [Fintype L] [Fintype F]
    [DecidableEq L] [DecidableEq F] (f : J ↪ L × F) (A : J → ℂ) (hA : cnormSq A = 1) :
    (sparseReduction f A).PosSemidef ∧ (sparseReduction f A).trace = 1 := by
  constructor
  · let v (l : L) (x : F) := Function.extend f A 0 (l, x)
    have he : sparseReduction f A = ∑ l, Matrix.vecMulVec (v l) (star (v l)) := by
      ext i j
      simp only [sparseReduction, Matrix.sum_apply, Matrix.vecMulVec, Matrix.of_apply,
        Pi.star_apply, v]
    rw [he]
    exact Matrix.posSemidef_sum _ (fun l _ => Matrix.posSemidef_vecMulVec_self_star (v l))
  · rw [Matrix.trace]
    change (∑ x : F, sparseReduction f A x x) = 1
    simp_rw [sparseReduction_diag]
    rw [Finset.sum_comm]
    have hsum (j : J) :
        (∑ x : F, if (f j).2 = x then ((‖A j‖ ^ 2 : ℝ) : ℂ) else 0) =
          ((‖A j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Finset.sum_eq_single (f j).2]
      · simp
      · intro x _ hx
        exact if_neg (Ne.symm hx)
      · exact fun h => (h (Finset.mem_univ _)).elim
    simp_rw [hsum]
    rw [← Complex.ofReal_sum, ← show cnormSq A = ∑ j, ‖A j‖ ^ 2 from rfl, hA, Complex.ofReal_one]

/-- The signal density of any retained set of sites in the sequential chain. -/
def maskedRunConditionalDensity {n : ℕ} (S : Finset (Fin n)) (A : RunAmplitudes n) :
    Matrix (RunAvailable S) (RunAvailable S) ℂ := sparseReduction (runSignature S) A.1

/-- Equal-prior success for binary readout with effects (1 + Y)/2 and (1 - Y)/2. -/
def pureReferenceMeasurementSuccess (v : ι → ℂ) (ρ Y : Matrix ι ι ℂ) : ℝ :=
  ((pureReferenceDensity v * ((1 / 2 : ℝ) • (1 + Y))).trace.re +
    (ρ * ((1 / 2 : ℝ) • (1 - Y))).trace.re) / 2

private theorem pureReferenceMeasurementSuccess_eq (v : ι → ℂ) {ρ : Matrix ι ι ℂ}
    (hv : cnormSq v = 1) (htr : ρ.trace = 1) (Y : Matrix ι ι ℂ) :
    pureReferenceMeasurementSuccess v ρ Y =
      (1 + ((pureReferenceGap v ρ * Y).trace).re / 2) / 2 := by
  have htrace : (pureReferenceDensity v).trace = 1 := by
    have h := pureReferenceGap_trace v hv htr
    rw [pureReferenceGap, Matrix.trace_sub, htr] at h
    exact sub_eq_zero.mp h
  unfold pureReferenceMeasurementSuccess pureReferenceGap
  rw [mul_smul_comm, mul_smul_comm, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, htrace, htr]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re, Complex.sub_re, Complex.one_re]
  ring

/-- The maximum binary success probability is attained and equals
one half plus one half of the trace distance. -/
theorem pureReference_optimal_readout (v : ι → ℂ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hv : cnormSq v = 1) (htr : ρ.trace = 1) :
    IsGreatest
      {p : ℝ | ∃ Y : Matrix ι ι ℂ, IsHermContraction Y ∧
        pureReferenceMeasurementSuccess v ρ Y = p}
      ((1 + pureReferenceDistance v ρ) / 2) := by
  have hD := pureReferenceGap_hermitian v hρ
  constructor
  · obtain ⟨Y, hY, he⟩ := exists_isHermContraction_re_trace_eq hD
    exact ⟨Y, hY, by rw [pureReferenceMeasurementSuccess_eq v hv htr Y, he, pureReferenceDistance]⟩
  · rintro p ⟨Y, hY, rfl⟩
    rw [pureReferenceMeasurementSuccess_eq v hv htr Y, pureReferenceDistance]
    have h := re_trace_mul_le_nuclearNorm hD hY
    linarith only [h]

/-- The readout problem for any retained set of sites in the chain has the
same scalar equation at positive distance. -/
theorem maskedRunReadout_eq_pos_iff_resolvent {n : ℕ} (S : Finset (Fin n))
    (A : RunAmplitudes n) {t : ℝ} (ht : 0 < t) :
    let v := (maskedRunEncoding S A).reference
    let ρ := maskedRunConditionalDensity S A
    pureReferenceDistance v ρ = t ↔
      cinner v ((ρ + (t : ℂ) • (1 : Matrix (RunAvailable S) (RunAvailable S) ℂ))⁻¹ *ᵥ v) = 1 := by
  obtain ⟨hp, htρ⟩ := sparseReduction_density (runSignature S) A.1 A.2
  exact pureReferenceDistance_eq_pos_iff_resolvent _ hp (maskedRunEncoding S A).reference_norm htρ ht

/-- At positive advantage the scalar equation gives precisely the
optimal success probability for any retained set of sites. -/
theorem maskedRunOptimalSuccess_iff_resolvent {n : ℕ} (S : Finset (Fin n))
    (A : RunAmplitudes n) {t : ℝ} (ht : 0 < t) :
    let v := (maskedRunEncoding S A).reference
    let ρ := maskedRunConditionalDensity S A
    IsGreatest
      {p : ℝ | ∃ Y : Matrix (RunAvailable S) (RunAvailable S) ℂ, IsHermContraction Y ∧
        pureReferenceMeasurementSuccess v ρ Y = p}
      ((1 + t) / 2) ↔
      cinner v ((ρ + (t : ℂ) • (1 : Matrix (RunAvailable S) (RunAvailable S) ℂ))⁻¹ *ᵥ v) = 1 := by
  obtain ⟨hp, htρ⟩ := sparseReduction_density (runSignature S) A.1 A.2
  let v := (maskedRunEncoding S A).reference
  let ρ := maskedRunConditionalDensity S A
  have hmax := pureReference_optimal_readout v (ρ := ρ) hp (maskedRunEncoding S A).reference_norm htρ
  have hroot := pureReferenceDistance_eq_pos_iff_resolvent v (ρ := ρ) hp
    (maskedRunEncoding S A).reference_norm htρ ht
  change IsGreatest _ ((1 + t) / 2) ↔
    cinner v ((ρ + (t : ℂ) • (1 : Matrix (RunAvailable S) (RunAvailable S) ℂ))⁻¹ *ᵥ v) = 1
  rw [← hroot]
  constructor
  · intro h
    have hval := le_antisymm (h.2 hmax.1) (hmax.2 h.1)
    linarith only [hval]
  · intro h
    simpa only [h] using hmax

#print axioms pureReferenceGap_eigenvector_iff
#print axioms pureReferenceDistance_eq_pos_iff_resolvent
#print axioms existsUnique_pureReference_resolvent_root
#print axioms no_pureReference_resolvent_root_iff_eq
#print axioms maskedRunReadout_eq_pos_iff_resolvent
#print axioms maskedRunOptimalSuccess_iff_resolvent

end

end GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch
