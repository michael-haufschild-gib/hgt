import GaloisForLFunctions.RHTower.ProlateSectorConstrainedSpectrum
import GaloisForLFunctions.RHTower.DepthSecularRootSpec
import GaloisForLFunctions.RHTower.ConstrainedProlateDepthVectorLimit
import GaloisForLFunctions.RHTower.ProlateSignedLadderEnvelope

/-!
# The constrained sector spectrum at every depth

`ProlateSectorConstrainedSpectrum` identifies the constrained eigenvalues of a Fourier sector in
the *first* spectral gap with the roots of the sector's secular function.  The fixed-mode spectral
ladder card needs the same identification in **every** gap `(d_k, d_{k+1})`.

Two things generalize.  The coordinate extraction — a constrained sector eigenvector has real
coordinate systems proportional to `ℓ` after the shift, and both satisfy the constraint — uses only
the index-`1` normalization and no gap data at all, so it is isolated here.  The collapse of the
constraint pairing to the secular function is then read at depth `k` through
`depthSecular_eq_tsum_mul_secularVector`, whose only inputs are a tail floor and a bound `μ < B`.
-/

noncomputable section

open Filter Set Topology
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-! ## The depth-`k` converse, abstractly -/

/-- **The depth-`k` converse in coordinates.**  A nonzero solution of the span-form constrained
eigen-system whose parameter stays below the tail floor forces the depth-`k` secular equation. -/
theorem depthSecular_eq_zero_of_constrained_eigen {d ℓ : ℕ → ℝ} {k : ℕ} {B μ c : ℝ}
    (hB : ∀ j, B ≤ d (j + (k + 2))) (hsum : Summable fun j => ℓ j ^ 2) (hμB : μ < B)
    (hpole : ∀ j, d j - μ ≠ 0) {v : ℕ → ℝ}
    (heig : ∀ j, d j * v j = μ * v j + c * ℓ j)
    (hconstraint : (∑' j : ℕ, ℓ j * v j) = 0) (hvne : v ≠ 0) :
    depthSecular d ℓ k μ = 0 := by
  have hv : ∀ j, v j = c * secularVector d ℓ μ j := by
    intro j
    have h2 : (d j - μ) * v j = c * ℓ j := by
      rw [sub_mul]
      linarith [heig j]
    have hne := hpole j
    rw [secularVector]
    field_simp
    linear_combination h2
  rcases eq_or_ne c 0 with hc0 | hcne
  · exfalso
    apply hvne
    funext j
    simp [hv j, hc0]
  · have hsummable : Summable fun j : ℕ => ℓ j * secularVector d ℓ μ j :=
      summable_mul_secularVector (k := k) hB hsum hμB
    have hcongr : ∀ j : ℕ, ℓ j * v j = c * (ℓ j * secularVector d ℓ μ j) := by
      intro j
      rw [hv j]
      ring
    have h0 : (∑' j : ℕ, ℓ j * v j) = c * depthSecular d ℓ k μ := by
      rw [tsum_congr hcongr, tsum_mul_left,
        depthSecular_eq_tsum_mul_secularVector (k := k) hB hsum hμB]
    have hzero : c * depthSecular d ℓ k μ = 0 := by rw [← h0, hconstraint]
    exact (mul_eq_zero.mp hzero).resolve_left hcne

/-! ## Coordinate extraction from a constrained sector eigenvector -/

/-- **The real coordinate system of a constrained sector eigenvector.**  Testing the weak
compressed eigenvalue equation against the elementary two-term constrained vectors gives a real
coordinate sequence proportional to the constraint sequence after the spectral shift, still
annihilated by the constraint.  No gap information is used. -/
theorem exists_constrained_coordinates_of_isSectorConstrainedEigen {a : ℝ} (ha : 0 < a)
    {σ : ℕ → ℕ} (hσ : Function.Injective σ) (hℓ1 : sectorCoord a σ 1 ≠ 0)
    {μ : ℝ} {g : evenSubspace} (hg : IsSectorConstrainedEigen a σ μ g) :
    ∃ (c : ℝ) (v : ℕ → ℝ), v ≠ 0 ∧
      (∀ j, sectorLeakage a σ j * v j = μ * v j + c * sectorCoord a σ j) ∧
      (∑' j : ℕ, sectorCoord a σ j * v j) = 0 := by
  classical
  set D : ℕ → ℝ := sectorLeakage a σ with hDdef
  set L : ℕ → ℝ := sectorCoord a σ with hLdef
  obtain ⟨x, hx⟩ := hg.expansion
  have hvon := orthonormal_sectorMode ha hσ
  have hBg := hasSum_leakage_apply (evenProlateLeakage_apply_sectorMode a σ) hx
  have hcoordB : ∀ j : ℕ,
      inner ℂ (sectorMode a σ j) (evenProlateLeakage a g) = ((D j : ℝ) : ℂ) * x j :=
    fun j => inner_eq_of_hasSum_smul hvon hBg j
  have hcoord : ∀ j : ℕ, inner ℂ (sectorMode a σ j) g = x j :=
    fun j => inner_eq_of_hasSum_smul hvon hx j
  have hdefect : ∀ j : ℕ,
      inner ℂ (evenProlateLeakage a g - ((μ : ℝ) : ℂ) • g) (sectorMode a σ j)
        = (starRingEnd ℂ) ((((D j - μ : ℝ)) : ℂ) * x j) := by
    intro j
    rw [inner_even_conj_symm (evenProlateLeakage a g - ((μ : ℝ) : ℂ) • g) (sectorMode a σ j)]
    congr 1
    rw [inner_even_sub_right, inner_even_smul_right, hcoordB j, hcoord j]
    push_cast
    ring
  have hpair : ∀ i k : ℕ, i ≠ k →
      ((L k : ℝ) : ℂ) * (starRingEnd ℂ) ((((D i - μ : ℝ)) : ℂ) * x i)
        + (-((L i : ℝ) : ℂ)) * (starRingEnd ℂ) ((((D k - μ : ℝ)) : ℂ) * x k) = 0 := by
    intro i k hik
    have hs := hasSum_sectorPair a σ hik ((L k : ℝ) : ℂ) (-((L i : ℝ) : ℂ))
    have hc : inner ℂ (evenCentralIndicator a)
        (((L k : ℝ) : ℂ) • sectorMode a σ i + (-((L i : ℝ) : ℂ)) • sectorMode a σ k) = 0 := by
      rw [inner_evenCentralIndicator_sectorPair]
      ring
    have h0 := hg.weak_eigen _ _ hs hc
    rw [inner_even_add_right, inner_even_smul_right, inner_even_smul_right,
      hdefect i, hdefect k] at h0
    exact h0
  set c : ℝ := (D 1 - μ) * (x 1).re / L 1 with hcdef
  set e : ℝ := (D 1 - μ) * (x 1).im / L 1 with hedef
  have hprop : ∀ j : ℕ, (D j - μ) * (x j).re = c * L j ∧ (D j - μ) * (x j).im = e * L j := by
    intro j
    rcases eq_or_ne j 1 with rfl | hj
    · constructor
      · rw [hcdef]; field_simp
      · rw [hedef]; field_simp
    · have h := hpair j 1 hj
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im, Complex.zero_re, Complex.zero_im] at hre him
      constructor
      · rw [hcdef]
        field_simp
        nlinarith [hre, him]
      · rw [hedef]
        field_simp
        nlinarith [hre, him]
  obtain ⟨hsu, hsw, hsdu, hsdw, hconu, hconw, e1, e2⟩ :=
    sector_real_parts ha hσ hx hg.constraint
  have hne : ∃ j : ℕ, x j ≠ 0 := by
    by_contra hall
    have hz : ∀ j : ℕ, x j = 0 := fun j => not_not.mp fun hj => hall ⟨j, hj⟩
    have hzero : (fun j : ℕ => x j • sectorMode a σ j) = fun _ : ℕ => (0 : evenSubspace) := by
      funext j
      rw [hz j, zero_smul]
    rw [hzero] at hx
    exact hg.ne_zero (hasSum_zero.unique hx).symm
  obtain ⟨j0, hj0⟩ := hne
  by_cases hu : (fun j : ℕ => (x j).re) = 0
  · have hwne : (fun j : ℕ => (x j).im) ≠ 0 := by
      intro hw
      apply hj0
      have h1 : (x j0).re = 0 := congrFun hu j0
      have h2 : (x j0).im = 0 := congrFun hw j0
      exact Complex.ext h1 h2
    exact ⟨e, fun j => (x j).im, hwne, fun j => by have := (hprop j).2; linarith, hconw⟩
  · exact ⟨c, fun j => (x j).re, hu, fun j => by have := (hprop j).1; linarith, hconu⟩

/-- Away from the `k`-th gap's own poles: no diagonal value meets a point of the gap. -/
theorem sectorLeakage_sub_ne_zero_of_mem_gap {a : ℝ} {σ : ℕ → ℕ} {k : ℕ} {μ : ℝ}
    (hhead : ∀ j, j ≤ k → sectorLeakage a σ j ≤ sectorLeakage a σ k)
    (hk12 : sectorLeakage a σ (k + 1) < sectorLeakage a σ (k + 2))
    (hfloor : ∀ j, sectorLeakage a σ (k + 2) ≤ sectorLeakage a σ (j + (k + 2)))
    (hμ : μ ∈ Ioo (sectorLeakage a σ k) (sectorLeakage a σ (k + 1))) :
    ∀ j, sectorLeakage a σ j - μ ≠ 0 := by
  intro j
  by_cases hj : j ≤ k
  · exact ne_of_lt (by linarith [hhead j hj, hμ.1])
  · have hjk : k < j := by omega
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hjk) with hj1 | hj1
    · exact ne_of_gt (by rw [← hj1]; linarith [hμ.2])
    · have hje : j = (j - (k + 2)) + (k + 2) := by omega
      have hfl := hfloor (j - (k + 2))
      rw [← hje] at hfl
      exact ne_of_gt (by linarith [hμ.2, hk12])

/-- **The depth-`k` converse for a prolate sector.**  A constrained eigenvalue of the compressed
leakage operator on the sector, lying in the `k`-th spectral gap, is a root of the sector's
depth-`k` secular function. -/
theorem depthSecular_eq_zero_of_isSectorConstrainedEigen {a : ℝ} (ha : 0 < a)
    {σ : ℕ → ℕ} (hσ : Function.Injective σ) {k : ℕ}
    (hhead : ∀ j, j ≤ k → sectorLeakage a σ j ≤ sectorLeakage a σ k)
    (hk12 : sectorLeakage a σ (k + 1) < sectorLeakage a σ (k + 2))
    (hfloor : ∀ j, sectorLeakage a σ (k + 2) ≤ sectorLeakage a σ (j + (k + 2)))
    (hℓ1 : sectorCoord a σ 1 ≠ 0)
    {μ : ℝ} (hμ : μ ∈ Ioo (sectorLeakage a σ k) (sectorLeakage a σ (k + 1)))
    {g : evenSubspace} (hg : IsSectorConstrainedEigen a σ μ g) :
    depthSecular (sectorLeakage a σ) (sectorCoord a σ) k μ = 0 := by
  obtain ⟨c, v, hvne, heig, hcon⟩ :=
    exists_constrained_coordinates_of_isSectorConstrainedEigen ha hσ hℓ1 hg
  have hsumL : Summable fun j : ℕ => sectorCoord a σ j ^ 2 := summable_sectorCoord_sq a hσ
  have hμB : μ < sectorLeakage a σ (k + 2) := lt_trans hμ.2 hk12
  have hpole : ∀ j, sectorLeakage a σ j - μ ≠ 0 :=
    sectorLeakage_sub_ne_zero_of_mem_gap hhead hk12 hfloor hμ
  exact depthSecular_eq_zero_of_constrained_eigen (k := k) hfloor hsumL hμB hpole heig hcon hvne


/-! ## The depth-`k` constrained eigenvector of a sector -/

/-- The depth-`k` secular coordinates of a sector. -/
def sectorDepthCoeff (a : ℝ) (σ : ℕ → ℕ) (k j : ℕ) : ℝ :=
  secularVector (sectorLeakage a σ) (sectorCoord a σ)
    (depthSecularRoot (sectorLeakage a σ) (sectorCoord a σ) k) j

/-- The depth-`k` secular coordinates synthesise an honest vector of the even carrier. -/
theorem exists_hasSum_sectorDepth {a : ℝ} (ha : 0 < a) {σ : ℕ → ℕ} (hσ : Function.Injective σ)
    {k : ℕ} (hsq : Summable fun j => sectorDepthCoeff a σ k j ^ 2) :
    ∃ f : evenSubspace,
      HasSum (fun j : ℕ => ((sectorDepthCoeff a σ k j : ℝ) : ℂ) • sectorMode a σ j) f := by
  refine exists_hasSum_sector ha hσ ?_
  refine hsq.congr fun j => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The depth-`k` sector vector is a constrained eigenvector of the compressed leakage
operator.**  Its leakage defect has constraint coordinates exactly `ℓ`, hence pairs with any vector
of the sector as the integral functional does and annihilates the constrained part. -/
theorem isSectorConstrainedEigen_depth {a : ℝ} (ha : 0 < a) {σ : ℕ → ℕ}
    (hσ : Function.Injective σ) {k : ℕ}
    (hpole : ∀ j, sectorLeakage a σ j
        - depthSecularRoot (sectorLeakage a σ) (sectorCoord a σ) k ≠ 0)
    (hsq : Summable fun j => sectorDepthCoeff a σ k j ^ 2)
    (hvne : sectorDepthCoeff a σ k ≠ 0)
    (hcon : (∑' j : ℕ, sectorCoord a σ j * sectorDepthCoeff a σ k j) = 0)
    {f : evenSubspace}
    (hf : HasSum (fun j : ℕ => ((sectorDepthCoeff a σ k j : ℝ) : ℂ) • sectorMode a σ j) f) :
    IsSectorConstrainedEigen a σ
      (depthSecularRoot (sectorLeakage a σ) (sectorCoord a σ) k) f := by
  classical
  set D : ℕ → ℝ := sectorLeakage a σ with hDdef
  set L : ℕ → ℝ := sectorCoord a σ with hLdef
  set μ : ℝ := depthSecularRoot D L k with hμdef
  set v : ℕ → ℝ := sectorDepthCoeff a σ k with hvdef
  have hvon := orthonormal_sectorMode ha hσ
  have hnormfun : (fun j : ℕ => ‖((v j : ℝ) : ℂ)‖ ^ 2) = fun j : ℕ => v j ^ 2 := by
    funext j
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hns : HasSum (fun j : ℕ => v j ^ 2) (‖f‖ ^ 2) := by
    have h := hasSum_norm_sq_of_hasSum_smul hvon hf
    rwa [hnormfun] at h
  obtain ⟨j0, hj0⟩ : ∃ j : ℕ, v j ≠ 0 := by
    by_contra hall
    exact hvne (funext fun j => by simpa using not_not.mp fun hj => hall ⟨j, hj⟩)
  have hfne : f ≠ 0 := by
    intro hzero
    have hle : v j0 ^ 2 ≤ ‖f‖ ^ 2 := le_hasSum hns j0 fun j _ => sq_nonneg _
    rw [hzero, norm_zero] at hle
    have hpos : (0 : ℝ) < v j0 ^ 2 := by positivity
    nlinarith [hle]
  have hsumL : Summable fun j : ℕ => L j ^ 2 := summable_sectorCoord_sq a hσ
  have hfcon : inner ℂ (evenCentralIndicator a) f = 0 := by
    have h := hasSum_constraint_of_hasSum_smul (inner_evenCentralIndicator_sectorMode a σ) hf
    have hreal : Summable fun j : ℕ => L j * v j := summable_mul_of_sq_summable hsumL hsq
    have hrs : HasSum (fun j : ℕ => L j * v j) 0 := by
      rw [← hcon]
      exact hreal.hasSum
    have h2 : HasSum (fun j : ℕ => (((L j * v j : ℝ)) : ℂ)) ((0 : ℝ) : ℂ) :=
      (Complex.hasSum_ofReal (f := fun j : ℕ => L j * v j) (x := 0)).mpr hrs
    have hcsfun : (fun j : ℕ => (((L j * v j : ℝ)) : ℂ))
        = fun j : ℕ => ((v j : ℝ) : ℂ) * ((L j : ℝ) : ℂ) := by
      funext j
      push_cast
      ring
    rw [hcsfun] at h2
    have huniq := h.unique h2
    simpa using huniq
  have hvterm : ∀ j : ℕ, (D j - μ) * v j = L j := by
    intro j
    have h : v j = L j / (D j - μ) := rfl
    rw [h, mul_comm, div_mul_cancel₀ _ (hpole j)]
  have hBf := hasSum_leakage_apply (evenProlateLeakage_apply_sectorMode a σ) hf
  have hcoordB : ∀ j : ℕ, inner ℂ (sectorMode a σ j) (evenProlateLeakage a f)
      = ((D j : ℝ) : ℂ) * ((v j : ℝ) : ℂ) :=
    fun j => inner_eq_of_hasSum_smul hvon hBf j
  have hcoord : ∀ j : ℕ, inner ℂ (sectorMode a σ j) f = ((v j : ℝ) : ℂ) :=
    fun j => inner_eq_of_hasSum_smul hvon hf j
  have hdefcoord : ∀ j : ℕ,
      inner ℂ (evenProlateLeakage a f - ((μ : ℝ) : ℂ) • f) (sectorMode a σ j)
        = ((L j : ℝ) : ℂ) := by
    intro j
    rw [inner_even_conj_symm (evenProlateLeakage a f - ((μ : ℝ) : ℂ) • f) (sectorMode a σ j),
      inner_even_sub_right, inner_even_smul_right, hcoordB j, hcoord j]
    have hreal : ((D j : ℝ) : ℂ) * ((v j : ℝ) : ℂ) - ((μ : ℝ) : ℂ) * ((v j : ℝ) : ℂ)
        = ((L j : ℝ) : ℂ) := by
      rw [← hvterm j]
      push_cast
      ring
    rw [hreal, Complex.conj_ofReal]
  refine ⟨⟨fun j => ((v j : ℝ) : ℂ), hf⟩, hfne, hfcon, ?_⟩
  intro z h hz hzcon
  have hmap : HasSum (fun j : ℕ =>
      inner ℂ (evenProlateLeakage a f - ((μ : ℝ) : ℂ) • f) (z j • sectorMode a σ j))
      (inner ℂ (evenProlateLeakage a f - ((μ : ℝ) : ℂ) • f) h) :=
    (innerSL ℂ (evenProlateLeakage a f - ((μ : ℝ) : ℂ) • f)).hasSum hz
  have hfun : (fun j : ℕ =>
      inner ℂ (evenProlateLeakage a f - ((μ : ℝ) : ℂ) • f) (z j • sectorMode a σ j))
      = fun j : ℕ => z j * ((L j : ℝ) : ℂ) := by
    funext j
    rw [inner_even_smul_right, hdefcoord j]
  rw [hfun] at hmap
  have hcs : HasSum (fun j : ℕ => z j * ((L j : ℝ) : ℂ)) 0 := by
    have hh := hasSum_constraint_of_hasSum_smul (inner_evenCentralIndicator_sectorMode a σ) hz
    rwa [hzcon] at hh
  exact hmap.unique hcs

/-! ## The Fourier-even sector, unconditionally, at every depth -/

/-- The structural data of the Fourier-even ladder at depth `k`, eventually in the aperture. -/
theorem eventually_positiveSector_depth_data (k : ℕ) :
    ∀ᶠ a : ℝ in atTop,
      0 < a ∧
      (∀ j, j ≤ k → sectorLeakage a positiveSectorIndex j
          ≤ sectorLeakage a positiveSectorIndex k) ∧
      sectorLeakage a positiveSectorIndex (k + 1) < sectorLeakage a positiveSectorIndex (k + 2) ∧
      (∀ j, sectorLeakage a positiveSectorIndex (k + 2)
          ≤ sectorLeakage a positiveSectorIndex (j + (k + 2))) ∧
      sectorCoord a positiveSectorIndex 1 ≠ 0 ∧
      sectorCoord a positiveSectorIndex (k + 1) ≠ 0 ∧
      depthSecularRoot (sectorLeakage a positiveSectorIndex) (sectorCoord a positiveSectorIndex) k
        ∈ Ioo (sectorLeakage a positiveSectorIndex k) (sectorLeakage a positiveSectorIndex (k + 1))
      ∧ depthSecular (sectorLeakage a positiveSectorIndex) (sectorCoord a positiveSectorIndex) k
          (depthSecularRoot (sectorLeakage a positiveSectorIndex)
            (sectorCoord a positiveSectorIndex) k) = 0
      ∧ (∑' j : ℕ, sectorCoord a positiveSectorIndex j
          * sectorDepthCoeff a positiveSectorIndex k j) = 0
      ∧ sectorDepthCoeff a positiveSectorIndex k ≠ 0
      ∧ Summable fun j : ℕ => sectorDepthCoeff a positiveSectorIndex k j ^ 2 := by
  have hpair := (constrainedProlateEven_exactEigenpair_and_allRawDefects k).1
  have hsq := ladderEnvelope_evenProlateSignedLeakage.ccm_depth_summable_secularVector_sq k
    evenProlateLadder_sum evenProlateLadder_bessel
    (fun j _ => tendsto_norm_evenProlateConstraintCoord_atTop j)
  have h1 : ∀ᶠ a : ℝ in atTop, ‖evenProlateConstraintCoord a (2 * 1)‖ ≠ 0 :=
    (tendsto_norm_evenProlateConstraintCoord_atTop 1).eventually_ne
      (constrainedProlateHermiteCoordinate_ne_zero 1)
  have hk1 : ∀ᶠ a : ℝ in atTop, ‖evenProlateConstraintCoord a (2 * (k + 1))‖ ≠ 0 :=
    (tendsto_norm_evenProlateConstraintCoord_atTop (k + 1)).eventually_ne
      (constrainedProlateHermiteCoordinate_ne_zero (k + 1))
  filter_upwards [hpair, hsq, h1, hk1,
    ladderEnvelope_evenProlateSignedLeakage.depth_struct k,
    eventually_gt_atTop (0 : ℝ)] with a hp hs ha1 hak1 hstruct ha
  exact ⟨ha, fun j hj => (hstruct.1.1 j hj).2, hstruct.1.2.2, hstruct.2, ha1, hak1,
    hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, hs⟩

/-- **Every gap of the Fourier-even sector carries a constrained eigenvector of the compressed
leakage operator, and its eigenvalue is the depth-`k` secular root.** -/
theorem eventually_exists_sectorDepthEigen_positive (k : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∃ f : evenSubspace,
      HasSum (fun j : ℕ => ((sectorDepthCoeff a positiveSectorIndex k j : ℝ) : ℂ)
        • sectorMode a positiveSectorIndex j) f ∧
      IsSectorConstrainedEigen a positiveSectorIndex
        (depthSecularRoot (fun j => evenProlateSignedLeakage a (2 * j))
          (fun j => ‖evenProlateConstraintCoord a (2 * j)‖) k) f := by
  filter_upwards [eventually_positiveSector_depth_data k] with a hd
  obtain ⟨ha, hhead, hk12, hfloor, -, -, hmem, -, hcon, hvne, hsq⟩ := hd
  obtain ⟨f, hf⟩ := exists_hasSum_sectorDepth ha positiveSectorIndex_injective hsq
  refine ⟨f, hf, ?_⟩
  exact isSectorConstrainedEigen_depth ha positiveSectorIndex_injective
    (sectorLeakage_sub_ne_zero_of_mem_gap hhead hk12 hfloor hmem) hsq hvne hcon hf

/-- **Exactly one constrained eigenvalue in each gap.**  Any constrained eigenvalue of the
compressed leakage operator on the Fourier-even sector lying in the `k`-th gap equals the depth-`k`
secular root. -/
theorem eventually_sectorDepthEigen_unique_positive (k : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ (μ : ℝ) (g : evenSubspace),
      μ ∈ Ioo (evenProlateSignedLeakage a (2 * k)) (evenProlateSignedLeakage a (2 * (k + 1))) →
      IsSectorConstrainedEigen a positiveSectorIndex μ g →
      μ = depthSecularRoot (fun j => evenProlateSignedLeakage a (2 * j))
            (fun j => ‖evenProlateConstraintCoord a (2 * j)‖) k := by
  filter_upwards [eventually_positiveSector_depth_data k] with a hd μ g hμ hg
  obtain ⟨ha, hhead, hk12, hfloor, h1, hk1, hmem, hroot, -, -, -⟩ := hd
  have hsumL : Summable fun j : ℕ => sectorCoord a positiveSectorIndex j ^ 2 :=
    summable_sectorCoord_sq a positiveSectorIndex_injective
  have hzero := depthSecular_eq_zero_of_isSectorConstrainedEigen ha positiveSectorIndex_injective
    hhead hk12 hfloor h1 hμ hg
  exact depthSecular_root_unique hk12 hfloor hhead hsumL hk1 hμ hmem hzero hroot

/-- **Equation `(8)` of the fixed-mode spectral ladder card, in the operator's own terms.**  For
every fixed depth `k`, the compressed leakage operator on the Fourier-even sector has, eventually,
exactly one constrained eigenvalue in the `k`-th spectral gap, and normalized by the next leakage
it converges to the exact Hermite contrast `theta_k = Q_k/Q_{k+1}`. -/
theorem constrainedProlateEven_operator_depth_ratio_tendsto (k : ℕ) :
    (∀ᶠ a : ℝ in atTop,
        (∃ f : evenSubspace, IsSectorConstrainedEigen a positiveSectorIndex
            (depthSecularRoot (fun j => evenProlateSignedLeakage a (2 * j))
              (fun j => ‖evenProlateConstraintCoord a (2 * j)‖) k) f) ∧
          (∀ (μ : ℝ) (g : evenSubspace),
            μ ∈ Ioo (evenProlateSignedLeakage a (2 * k))
              (evenProlateSignedLeakage a (2 * (k + 1))) →
            IsSectorConstrainedEigen a positiveSectorIndex μ g →
            μ = depthSecularRoot (fun j => evenProlateSignedLeakage a (2 * j))
                  (fun j => ‖evenProlateConstraintCoord a (2 * j)‖) k)) ∧
      Tendsto (fun a : ℝ =>
          depthSecularRoot (fun j => evenProlateSignedLeakage a (2 * j))
            (fun j => ‖evenProlateConstraintCoord a (2 * j)‖) k
            / evenProlateSignedLeakage a (2 * (k + 1)))
        atTop (𝓝 (constrainedProlateHermiteTheta k)) := by
  refine ⟨?_, constrainedProlateEven_depth_ratio_tendsto k⟩
  filter_upwards [eventually_exists_sectorDepthEigen_positive k,
    eventually_sectorDepthEigen_unique_positive k] with a hex huniq
  exact ⟨⟨hex.choose, hex.choose_spec.2⟩, huniq⟩

/-- **Equation `(9)` of the fixed-mode spectral ladder card, in the operator's own terms.**  Two
consecutive constrained eigenvalues of the compressed leakage operator, corrected by the ratio of
their dominant leakages, separate by the Hermite quotient `theta_{k+1}/theta_k`. -/
theorem constrainedProlateEven_operator_adjacent_ratio_tendsto (k : ℕ) :
    Tendsto (fun a : ℝ =>
        depthSecularRoot (fun j => evenProlateSignedLeakage a (2 * j))
            (fun j => ‖evenProlateConstraintCoord a (2 * j)‖) (k + 1)
          / depthSecularRoot (fun j => evenProlateSignedLeakage a (2 * j))
              (fun j => ‖evenProlateConstraintCoord a (2 * j)‖) k
          * (evenProlateSignedLeakage a (2 * (k + 1))
              / evenProlateSignedLeakage a (2 * (k + 2))))
      atTop (𝓝 (constrainedProlateHermiteTheta (k + 1) / constrainedProlateHermiteTheta k)) :=
  constrainedProlateEven_adjacent_ratio_tendsto k

/-- **Equations `(10)`--`(11)` of the fixed-mode spectral ladder card, in the operator's own
terms.**  The coefficients of the depth-`k` constrained eigenvector against the sector's
orthonormal prolate family are exactly the depth-`k` secular coordinates, whose oriented
normalization converges in `ell^2` to the canonical Hermite contrast unit — an orthonormal family. -/
theorem constrainedProlateEven_operator_depth_eigenvector_coeff (k : ℕ) :
    (∀ᶠ a : ℝ in atTop, ∀ f : evenSubspace,
        HasSum (fun j : ℕ => ((sectorDepthCoeff a positiveSectorIndex k j : ℝ) : ℂ)
          • sectorMode a positiveSectorIndex j) f →
        ∀ j : ℕ, inner ℂ (sectorMode a positiveSectorIndex j) f
          = ((sectorDepthCoeff a positiveSectorIndex k j : ℝ) : ℂ)) ∧
      Tendsto (fun a : ℝ =>
        let V := (secularVector (fun j => evenProlateSignedLeakage a (2 * j))
            (fun j => ‖evenProlateConstraintCoord a (2 * j)‖)
            (depthSecularRoot (fun j => evenProlateSignedLeakage a (2 * j))
              (fun j => ‖evenProlateConstraintCoord a (2 * j)‖) k) 0)⁻¹ •
          secularLp (fun j => evenProlateSignedLeakage a (2 * j))
            (fun j => ‖evenProlateConstraintCoord a (2 * j)‖)
            (depthSecularRoot (fun j => evenProlateSignedLeakage a (2 * j))
              (fun j => ‖evenProlateConstraintCoord a (2 * j)‖) k)
        (‖V‖)⁻¹ • V) atTop (𝓝 (-hermiteContrastUnit k)) ∧
      Orthonormal ℝ hermiteContrastUnit := by
  refine ⟨?_, constrainedProlateEven_normalized_eigenvector_tendsto k,
    orthonormal_hermiteContrastUnit⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha f hf j
  exact inner_eq_of_hasSum_smul (orthonormal_sectorMode ha positiveSectorIndex_injective) hf j

end RHTower

end
