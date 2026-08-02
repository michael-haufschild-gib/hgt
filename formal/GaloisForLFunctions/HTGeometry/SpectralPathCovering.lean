import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch
import GaloisForLFunctions.HTGeometry.PolynomialMatrixSimpleSpectrumTransport
import GaloisForLFunctions.Bottcher.BranchContinuation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic

/-!
# Spectral path covering and unconditional root continuation

For every continuous finite matrix path with simple characteristic roots,
the characteristic-root incidence space is a finite covering of the unit
interval.  Compactness follows from a uniform Cauchy root bound; local
homeomorphism charts are restrictions of the holomorphic implicit-function
chart at each simple root.  Covering-space path lifting then gives global,
continuous, unique continuation of every initial eigenvalue.  The final
theorems specialize this mechanism to polynomial matrix paths whose fixed-size
characteristic resultant never vanishes.
-/

open Filter Topology Set unitInterval
open scoped ContDiff
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

def SpectralPathRoot
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (H : I → Matrix J J ℂ) :=
  {q : I × ℂ |
    matrixCharpolyRelation (H q.1, q.2) = 0}

def spectralPathProjection
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {H : I → Matrix J J ℂ}
    (q : SpectralPathRoot H) : I :=
  q.1.1

theorem spectralPathRoot_charpoly_eval
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {H : I → Matrix J J ℂ}
    (q : SpectralPathRoot H) :
    (H q.1.1).charpoly.eval q.1.2 = 0 := by
  rw [Matrix.eval_charpoly]
  exact q.2

theorem continuous_matrixCharpolyRelation
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J] :
    Continuous (matrixCharpolyRelation (ι := J)) := by
  rw [continuous_iff_continuousAt]
  exact fun q =>
    (matrixCharpolyRelation_analyticAt q).continuousAt

theorem continuous_spectralPathRelation
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {H : I → Matrix J J ℂ} (hH : Continuous H) :
    Continuous fun q : I × ℂ =>
      matrixCharpolyRelation (H q.1, q.2) := by
  exact continuous_matrixCharpolyRelation.comp
    ((hH.comp continuous_fst).prodMk continuous_snd)

theorem continuous_charpoly_coeff
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {H : I → Matrix J J ℂ} (hH : Continuous H) (k : ℕ) :
    Continuous fun s : I => (H s).charpoly.coeff k := by
  by_cases hk : k ≤ Fintype.card J
  · let l := Fintype.card J - k
    have hl : l ≤ Fintype.card J := Nat.sub_le _ _
    have hindex : Fintype.card J - l = k := by
      omega
    have heq :
        (fun s : I => (H s).charpoly.coeff k) =
          fun s =>
            (-1 : ℂ) ^ l *
              ∑ A ∈ Finset.univ.powersetCard l,
                ((H s).submatrix
                  (Subtype.val : A → J)
                  (Subtype.val : A → J)).det := by
      funext s
      rw [← hindex,
        Matrix.charpoly_coeff_eq_sum_minors (H s) l hl]
    rw [heq]
    apply continuous_const.mul
    apply continuous_finsetSum
    intro A _hA
    apply Continuous.matrix_det
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    exact
      (continuous_apply (Subtype.val b)).comp
        ((continuous_apply (Subtype.val a)).comp hH)
  · have hklt : Fintype.card J < k := Nat.lt_of_not_ge hk
    have heq :
        (fun s : I => (H s).charpoly.coeff k) =
          fun _ => 0 := by
      funext s
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (by simpa [Matrix.charpoly_natDegree_eq_dim] using hklt)
    rw [heq]
    exact continuous_const

theorem exists_spectralPath_rootNorm_bound
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {H : I → Matrix J J ℂ} (hH : Continuous H) :
    ∃ R : ℝ, ∀ q : SpectralPathRoot H, ‖q.1.2‖ ≤ R := by
  let C : I → ℝ := fun s =>
    ∑ i ∈ Finset.range (Fintype.card J),
      ‖(H s).charpoly.coeff i‖
  have hC : Continuous C := by
    apply continuous_finsetSum
    intro i _hi
    exact (continuous_charpoly_coeff hH i).norm
  have hK : IsCompact (Set.univ : Set I) := isCompact_univ
  obtain ⟨smax, _hsmax, hmax⟩ :=
    hK.exists_isMaxOn Set.univ_nonempty hC.continuousOn
  refine ⟨max 1 (C smax), fun q => ?_⟩
  have hroot :=
    Bottcher.norm_root_le_of_monic
      (H q.1.1).charpoly_monic
      (spectralPathRoot_charpoly_eval q)
      (by simpa [Matrix.charpoly_natDegree_eq_dim] using
        (Fintype.card_pos : 0 < Fintype.card J))
  have hroot' : ‖q.1.2‖ ≤ max 1 (C q.1.1) := by
    simpa [C, Matrix.charpoly_natDegree_eq_dim] using hroot
  exact hroot'.trans
    (max_le_max_left 1 (hmax (Set.mem_univ q.1.1)))

theorem isCompact_spectralPathRoot_set
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {H : I → Matrix J J ℂ} (hH : Continuous H) :
    IsCompact {q : I × ℂ |
      matrixCharpolyRelation (H q.1, q.2) = 0} := by
  obtain ⟨R, hR⟩ :=
    exists_spectralPath_rootNorm_bound hH
  have hclosed :
      IsClosed {q : I × ℂ |
        matrixCharpolyRelation (H q.1, q.2) = 0} :=
    isClosed_eq
      (continuous_spectralPathRelation hH)
      continuous_const
  have hcompact :
      IsCompact
        ((Set.univ : Set I) ×ˢ Metric.closedBall (0 : ℂ) R) :=
    isCompact_univ.prod (isCompact_closedBall 0 R)
  apply hcompact.of_isClosed_subset hclosed
  intro q hq
  refine ⟨Set.mem_univ q.1, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hR ⟨q, hq⟩

theorem spectralPathRoot_partial_ne
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {H : I → Matrix J J ℂ}
    (hsep : ∀ s : I, (H s).charpoly.Separable)
    (q : SpectralPathRoot H) :
    (fderiv ℂ (matrixCharpolyRelation (ι := J))
      (H q.1.1, q.1.2)) (0, 1) ≠ 0 := by
  rw [matrixCharpolyRelation_partial_w]
  exact
    (hsep q.1.1).eval₂_derivative_ne_zero
      (RingHom.id ℂ)
      (spectralPathRoot_charpoly_eval q)

noncomputable def spectralIFTData
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {H : I → Matrix J J ℂ}
    (hsep : ∀ s : I, (H s).charpoly.Separable)
    (q : SpectralPathRoot H) :
    ImplicitFunctionData ℂ (Matrix J J ℂ × ℂ) ℂ
      (Matrix J J ℂ) := by
  let f := matrixCharpolyRelation (ι := J)
  let u : Matrix J J ℂ × ℂ := (H q.1.1, q.1.2)
  have cdf : ContDiffAt ℂ ω f u :=
    (matrixCharpolyRelation_analyticAt u).contDiffAt
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by decide
  have if₂ :
      (fderiv ℂ f u ∘L
        (.inr ℂ (Matrix J J ℂ) ℂ)).IsInvertible :=
    HolomorphicIFT.clm_invertible_of_apply_one_ne
      (by simpa [f, u] using
        spectralPathRoot_partial_ne hsep q)
  exact
    cdf.hasStrictFDerivAt hω
      |>.implicitFunctionDataOfProdDomain if₂

theorem spectralIFTData_apply
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {H : I → Matrix J J ℂ}
    (hsep : ∀ s : I, (H s).charpoly.Separable)
    (q : SpectralPathRoot H)
    (v : Matrix J J ℂ × ℂ) :
    (spectralIFTData hsep q).toOpenPartialHomeomorph v =
      (matrixCharpolyRelation v, v.1) := by
  rfl

theorem spectralIFTData_mem_source
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {H : I → Matrix J J ℂ}
    (hsep : ∀ s : I, (H s).charpoly.Separable)
    (q : SpectralPathRoot H) :
    (H q.1.1, q.1.2) ∈
      (spectralIFTData hsep q).toOpenPartialHomeomorph.source := by
  exact
    ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _

theorem isLocalHomeomorph_spectralPathProjection
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {H : I → Matrix J J ℂ}
    (hH : Continuous H)
    (hsep : ∀ s : I, (H s).charpoly.Separable) :
    IsLocalHomeomorph
      (spectralPathProjection (H := H)) := by
  classical
  intro e
  let data := spectralIFTData hsep e
  let ψ := data.toOpenPartialHomeomorph
  let ambient : SpectralPathRoot H →
      Matrix J J ℂ × ℂ :=
    fun q => (H q.1.1, q.1.2)
  let baseTarget : I → ℂ × Matrix J J ℂ :=
    fun s => (0, H s)
  have hambient : Continuous ambient := by
    apply Continuous.prodMk
    · exact hH.comp
        (continuous_fst.comp continuous_subtype_val)
    · exact continuous_snd.comp continuous_subtype_val
  have hbaseTarget : Continuous baseTarget :=
    continuous_const.prodMk hH
  let targetPred : I → Prop :=
    fun s => baseTarget s ∈ ψ.target
  let liftRoot (s : I) (hs : targetPred s) :
      SpectralPathRoot H := by
    let v := ψ.symm (baseTarget s)
    have hright := ψ.right_inv hs
    have hrel : matrixCharpolyRelation v = 0 := by
      have h := congrArg Prod.fst hright
      simpa [ψ, data, spectralIFTData_apply,
        baseTarget, v] using h
    have hmatrix : v.1 = H s := by
      have h := congrArg Prod.snd hright
      simpa [ψ, data, spectralIFTData_apply,
        baseTarget, v] using h
    refine ⟨(s, v.2), ?_⟩
    change matrixCharpolyRelation (H s, v.2) = 0
    rw [← hmatrix]
    exact hrel
  let invRoot : I → SpectralPathRoot H :=
    fun s =>
      if hs : targetPred s then liftRoot s hs else e
  let source : Set (SpectralPathRoot H) :=
    ambient ⁻¹' ψ.source
  let target : Set I :=
    baseTarget ⁻¹' ψ.target
  have hmapSource :
      ∀ q ∈ source,
        spectralPathProjection q ∈ target := by
    intro q hq
    have heq :
        ψ (ambient q) =
          baseTarget (spectralPathProjection q) := by
      rw [spectralIFTData_apply]
      apply Prod.ext
      · exact q.2
      · rfl
    show baseTarget (spectralPathProjection q) ∈ ψ.target
    rw [← heq]
    exact ψ.map_source hq
  have hambientLift :
      ∀ s (hs : targetPred s),
        ambient (liftRoot s hs) =
          ψ.symm (baseTarget s) := by
    intro s hs
    let v := ψ.symm (baseTarget s)
    have hright := ψ.right_inv hs
    have hmatrix : v.1 = H s := by
      have h := congrArg Prod.snd hright
      simpa [ψ, data, spectralIFTData_apply,
        baseTarget, v] using h
    apply Prod.ext
    · exact hmatrix.symm
    · rfl
  have hmapTarget :
      ∀ s ∈ target, invRoot s ∈ source := by
    intro s hs
    have hs' : targetPred s := hs
    rw [show invRoot s = liftRoot s hs' by
      dsimp only [invRoot]
      rw [dif_pos hs']]
    change ambient (liftRoot s hs') ∈ ψ.source
    rw [hambientLift s hs']
    exact ψ.map_target hs'
  have hleft :
      ∀ q ∈ source,
        invRoot (spectralPathProjection q) = q := by
    intro q hq
    have htarget :=
      hmapSource q hq
    have hs' : targetPred
        (spectralPathProjection q) := htarget
    rw [show invRoot (spectralPathProjection q) =
        liftRoot (spectralPathProjection q) hs' by
      dsimp only [invRoot]
      rw [dif_pos hs']]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have heq :
          ψ (ambient q) =
            baseTarget (spectralPathProjection q) := by
        rw [spectralIFTData_apply]
        apply Prod.ext
        · exact q.2
        · rfl
      have hleftψ := ψ.left_inv hq
      have hv :
          ψ.symm
              (baseTarget
                (spectralPathProjection q)) =
            ambient q := by
        rw [← heq]
        exact hleftψ
      have hamb :=
        hambientLift
          (spectralPathProjection q) hs'
      exact congrArg
        (fun v : Matrix J J ℂ × ℂ => v.2)
        (hamb.trans hv)
  have hright :
      ∀ s ∈ target,
        spectralPathProjection (invRoot s) = s := by
    intro s hs
    have hs' : targetPred s := hs
    rw [show invRoot s = liftRoot s hs' by
      dsimp only [invRoot]
      rw [dif_pos hs']]
    rfl
  have hcontInv : ContinuousOn invRoot target := by
    have hψsymm :
        ContinuousOn
          (fun s => ψ.symm (baseTarget s)) target :=
      ψ.continuousOn_symm.comp
        hbaseTarget.continuousOn
        (fun s hs => hs)
    have hpair :
        ContinuousOn
          (fun s =>
            (s, (ψ.symm (baseTarget s)).2)) target :=
      continuousOn_id.prodMk
        (continuous_snd.comp_continuousOn hψsymm)
    rw [continuousOn_iff_continuous_restrict]
    apply Continuous.subtype_mk
    have hpairRestr :
        Continuous fun s : target =>
          (s.1, (ψ.symm (baseTarget s.1)).2) :=
      continuousOn_iff_continuous_restrict.mp hpair
    convert hpairRestr using 1
    funext s
    have hs' : targetPred s.1 := s.2
    change
      (invRoot s.1).1 =
        (s.1, (ψ.symm (baseTarget s.1)).2)
    rw [show invRoot s.1 = liftRoot s.1 hs' by
      dsimp only [invRoot]
      rw [dif_pos hs']]
  let chart : OpenPartialHomeomorph
      (SpectralPathRoot H) I := {
    toFun := spectralPathProjection
    invFun := invRoot
    source := source
    target := target
    map_source' := hmapSource
    map_target' := hmapTarget
    left_inv' := hleft
    right_inv' := hright
    continuousOn_toFun :=
      (continuous_fst.comp continuous_subtype_val).continuousOn
    continuousOn_invFun := hcontInv
    open_source := (ψ.open_source).preimage hambient
    open_target := (ψ.open_target).preimage hbaseTarget
  }
  refine ⟨chart, ?_, rfl⟩
  exact spectralIFTData_mem_source hsep e

theorem isCoveringMap_spectralPathProjection
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {H : I → Matrix J J ℂ}
    (hH : Continuous H)
    (hsep : ∀ s : I, (H s).charpoly.Separable) :
    IsCoveringMap
      (spectralPathProjection (H := H)) := by
  letI : CompactSpace (SpectralPathRoot H) :=
    isCompact_iff_compactSpace.mp
      (isCompact_spectralPathRoot_set hH)
  rw [← isLocalHomeomorph_iff_isCoveringMap]
  exact
    isLocalHomeomorph_spectralPathProjection hH hsep

theorem exists_continuous_charpolyRoot_lift
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    {H : I → Matrix J J ℂ}
    (hH : Continuous H)
    (hsep : ∀ s : I, (H s).charpoly.Separable)
    {w₀ : ℂ} (hw₀ : (H 0).charpoly.eval w₀ = 0) :
    ∃ root : I → ℂ,
      Continuous root ∧
      root 0 = w₀ ∧
      ∀ s : I, (H s).charpoly.eval (root s) = 0 := by
  have hrel₀ :
      matrixCharpolyRelation (H 0, w₀) = 0 := by
    unfold matrixCharpolyRelation
    rw [← Matrix.eval_charpoly]
    exact hw₀
  let e₀ : SpectralPathRoot H :=
    ⟨(0, w₀), hrel₀⟩
  let cov :=
    isCoveringMap_spectralPathProjection hH hsep
  let base : C(I, I) := ContinuousMap.id I
  have hbase :
      base 0 =
        spectralPathProjection e₀ := rfl
  let lifted : C(I, SpectralPathRoot H) :=
    cov.liftPath base e₀ hbase
  let root : I → ℂ :=
    fun s => (lifted s).1.2
  refine ⟨root, ?_, ?_, ?_⟩
  · exact
      (continuous_snd.comp continuous_subtype_val).comp
        lifted.continuous
  · have hzero := cov.liftPath_zero base e₀ hbase
    exact congrArg (fun q : SpectralPathRoot H => q.1.2)
      hzero
  · intro s
    have hlifts := congrFun
      (cov.liftPath_lifts base e₀ hbase) s
    have htime :
        (lifted s).1.1 = s := by
      exact hlifts
    have hroot :=
      spectralPathRoot_charpoly_eval (lifted s)
    simpa [root, htime] using hroot

theorem matrixCharpoly_separable_of_resultant_eval_ne_zero
    {θ J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (M : Matrix J J (MvPolynomial θ ℂ))
    (p : θ → ℂ)
    (hres :
      MvPolynomial.eval p
        (matrixCharacteristicResultantPolynomial M) ≠ 0) :
    ((M.map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) p)).charpoly).Separable := by
  let H :=
    M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) p)
  have hfixed :
      Polynomial.resultant H.charpoly H.charpoly.derivative
        (Fintype.card J) (Fintype.card J - 1) ≠ 0 := by
    change
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) p)
        (matrixCharacteristicResultantPolynomial M) ≠ 0 at hres
    rw [eval_matrixCharacteristicResultantPolynomial] at hres
    exact hres
  have hcanonical :
      Polynomial.resultant H.charpoly
        H.charpoly.derivative ≠ 0 := by
    simpa [Matrix.charpoly_natDegree_eq_dim,
      Polynomial.natDegree_derivative] using hfixed
  have hcoprime :
      IsCoprime H.charpoly H.charpoly.derivative := by
    by_contra hnot
    have hzero :
        Polynomial.resultant H.charpoly
          H.charpoly.derivative = 0 :=
      Polynomial.resultant_eq_zero_iff.mpr
        ⟨Or.inl H.charpoly_monic.ne_zero, hnot⟩
    exact hcanonical hzero
  exact (Polynomial.separable_def H.charpoly).mpr hcoprime

theorem continuous_eval_polynomialMatrix_path
    {θ J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J (MvPolynomial θ ℂ))
    {p₀ p₁ : θ → ℂ} (path : Path p₀ p₁) :
    Continuous fun s : I =>
      M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (path s)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous fun s : I =>
    MvPolynomial.eval (path s) (M i j)
  exact (MvPolynomial.continuous_eval (M i j)).comp
    path.continuous

theorem exists_continuous_polynomialMatrixRoot_lift
    {θ J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (M : Matrix J J (MvPolynomial θ ℂ))
    {p₀ p₁ : θ → ℂ} (path : Path p₀ p₁)
    (hres : ∀ s : I,
      MvPolynomial.eval (path s)
        (matrixCharacteristicResultantPolynomial M) ≠ 0)
    {w₀ : ℂ}
    (hw₀ :
      ((M.map (MvPolynomial.eval₂Hom
        (RingHom.id ℂ) p₀)).charpoly).eval w₀ = 0) :
    ∃ root : I → ℂ,
      Continuous root ∧
      root 0 = w₀ ∧
      ∀ s : I,
        ((M.map (MvPolynomial.eval₂Hom
          (RingHom.id ℂ) (path s))).charpoly).eval
            (root s) = 0 := by
  let H : I → Matrix J J ℂ :=
    fun s =>
      M.map (MvPolynomial.eval₂Hom
        (RingHom.id ℂ) (path s))
  have hH : Continuous H :=
    continuous_eval_polynomialMatrix_path M path
  have hsep : ∀ s : I, (H s).charpoly.Separable :=
    fun s =>
      matrixCharpoly_separable_of_resultant_eval_ne_zero
        M (path s) (hres s)
  have hw₀' : (H 0).charpoly.eval w₀ = 0 := by
    simpa [H] using hw₀
  simpa [H] using
    exists_continuous_charpolyRoot_lift
      hH hsep hw₀'

end GaloisForLFunctions.HTGeometry
