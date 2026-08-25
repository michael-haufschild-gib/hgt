import GaloisForLFunctions.HTGeometry.AdjointGramChannelPeeling
import GaloisForLFunctions.HTGeometry.FiniteGramSpectralPeeling

open Complex Filter Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

noncomputable def rectangularMatrixVecLinearEquiv
    (I J : Type*) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    Matrix I J ℂ ≃ₗ[ℂ] ((J × I) → ℂ) :=
  LinearEquiv.ofBijective
    { toFun := Matrix.vec
      map_add' := Matrix.vec_add
      map_smul' := Matrix.vec_smul }
    Matrix.vec_bijective

/-- On a finite rectangular matrix space, entrywise convergence is matrix-norm convergence. -/
theorem finiteMatrix_tendsto_of_tendsto_entries
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {α : Type*} {l : Filter α} (U : α → Matrix I J ℂ) (U₀ : Matrix I J ℂ)
    (hU : ∀ i j, Tendsto (fun t => U t i j) l (𝓝 (U₀ i j))) :
    Tendsto U l (𝓝 U₀) := by
  let e := rectangularMatrixVecLinearEquiv I J
  have hvec : Tendsto (fun t => e (U t)) l (𝓝 (e U₀)) := by
    rw [tendsto_pi_nhds]
    intro ij
    simpa [e, rectangularMatrixVecLinearEquiv, Matrix.vec] using hU ij.2 ij.1
  have hback := e.toContinuousLinearEquiv.symm.continuous.tendsto (e U₀)
  have hback' := hback.comp hvec
  convert hback' using 1
  · funext t
    exact (e.symm_apply_apply (U t)).symm
  · exact congrArg nhds (e.symm_apply_apply U₀).symm

theorem inner_channelGramDefect_of_mem
    (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (L : E →L[ℂ] F) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    inner ℂ (channelGramDefect S L x) y =
      inner ℂ (L x) (L y) - inner ℂ x y := by
  rw [channelGramDefect, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    S.starProjection_eq_self_iff.mpr hx]
  rw [inner_sub_left]
  have hproj : inner ℂ (S.starProjection (L.adjoint (L x))) y =
      inner ℂ (L.adjoint (L x)) y := by
    calc
      inner ℂ (S.starProjection (L.adjoint (L x))) y =
          inner ℂ (L.adjoint (L x)) (S.starProjection y) :=
        S.starProjection_isSymmetric _ _
      _ = inner ℂ (L.adjoint (L x)) y := by
        rw [S.starProjection_eq_self_iff.mpr hy]
  rw [hproj, ContinuousLinearMap.adjoint_inner_left]

theorem inner_channelOffDiagonalGram_of_mem_orthogonal
    (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (L : E →L[ℂ] F) {x y : E} (hx : x ∈ Sᗮ) (hy : y ∈ S) :
    inner ℂ (channelOffDiagonalGram S L y) x =
      inner ℂ (L y) (L x) := by
  rw [channelOffDiagonalGram, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    S.starProjection_eq_self_iff.mpr hy, sub_apply,
    ContinuousLinearMap.id_apply]
  rw [inner_sub_left]
  have hzero : inner ℂ (S.starProjection (L.adjoint (L y))) x = 0 :=
    hx _ (S.starProjection_apply_mem _)
  rw [hzero, sub_zero, ContinuousLinearMap.adjoint_inner_left]

def finiteLeakagePersistentGram {n : ℕ}
    (L : E →L[ℂ] F) (v : Fin n → E) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => inner ℂ (L (v j)) (L (v k))

def finiteLeakageCrossGram {n m : ℕ}
    (L : E →L[ℂ] F) (v : Fin n → E) (w : Fin m → E) :
    Matrix (Fin n) (Fin m) ℂ :=
  fun j k => inner ℂ (L (v j)) (L (w k))

def finiteLeakageCrossingGram {m : ℕ}
    (L : E →L[ℂ] F) (w : Fin m → E) : Matrix (Fin m) (Fin m) ℂ :=
  fun j k => inner ℂ (L (w j)) (L (w k))

def finiteLeakageSplitGram {n m : ℕ}
    (L : E →L[ℂ] F) (v : Fin n → E) (w : Fin m → E) :
    Matrix (Fin (n + m)) (Fin (n + m)) ℂ :=
  finiteHermitianBlock (finiteLeakagePersistentGram L v)
    (finiteLeakageCrossGram L v w) (finiteLeakageCrossingGram L w)

theorem finiteLeakagePersistentGram_isHermitian {n : ℕ}
    (L : E →L[ℂ] F) (v : Fin n → E) :
    (finiteLeakagePersistentGram L v).IsHermitian := by
  ext j k
  exact inner_conj_symm _ _

theorem finiteLeakageCrossingGram_isHermitian {m : ℕ}
    (L : E →L[ℂ] F) (w : Fin m → E) :
    (finiteLeakageCrossingGram L w).IsHermitian := by
  ext j k
  exact inner_conj_symm _ _

theorem finiteLeakageSplitGram_isHermitian {n m : ℕ}
    (L : E →L[ℂ] F) (v : Fin n → E) (w : Fin m → E) :
    (finiteLeakageSplitGram L v w).IsHermitian :=
  finiteHermitianBlock_isHermitian
    (finiteLeakagePersistentGram_isHermitian L v)
    (finiteLeakageCrossingGram_isHermitian L w)

theorem tendsto_finiteLeakageCrossingGram_one_of_channelDefect
    {m : ℕ} {ι : Type*} {l : Filter ι}
    (S : ι → Submodule ℂ E) [∀ i, (S i).HasOrthogonalProjection]
    (L : ι → E →L[ℂ] F) (w : ∀ i, Fin m → E)
    (hwmem : ∀ i j, w i j ∈ S i)
    (hwnorm : ∀ i j, ‖w i j‖ = 1)
    (hwinner : ∀ i j k, inner ℂ (w i j) (w i k) =
      (1 : Matrix (Fin m) (Fin m) ℂ) j k)
    (hdef : Tendsto (fun i => ‖channelGramDefect (S i) (L i)‖) l (𝓝 0)) :
    Tendsto (fun i => finiteLeakageCrossingGram (L i) (w i)) l
      (𝓝 (1 : Matrix (Fin m) (Fin m) ℂ)) := by
  apply finiteMatrix_tendsto_of_tendsto_entries
  intro j k
  change Tendsto (fun i => inner ℂ (L i (w i j)) (L i (w i k))) l
    (𝓝 ((1 : Matrix (Fin m) (Fin m) ℂ) j k))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hdef
  have hid := inner_channelGramDefect_of_mem (S i) (L i)
    (hwmem i j) (hwmem i k)
  have heq : inner ℂ (L i (w i j)) (L i (w i k)) -
      (1 : Matrix (Fin m) (Fin m) ℂ) j k =
        inner ℂ (channelGramDefect (S i) (L i) (w i j)) (w i k) := by
    rw [← hwinner i j k]
    exact hid.symm
  rw [heq]
  calc
    ‖inner ℂ (channelGramDefect (S i) (L i) (w i j)) (w i k)‖ ≤
        ‖channelGramDefect (S i) (L i) (w i j)‖ * ‖w i k‖ :=
      norm_inner_le_norm _ _
    _ ≤ (‖channelGramDefect (S i) (L i)‖ * ‖w i j‖) * ‖w i k‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖channelGramDefect (S i) (L i)‖ := by
      rw [hwnorm i j, hwnorm i k]
      ring

theorem tendsto_finiteLeakageCrossGram_zero_of_channelOffDiagonal
    {n m : ℕ} {ι : Type*} {l : Filter ι}
    (S : ι → Submodule ℂ E) [∀ i, (S i).HasOrthogonalProjection]
    (L : ι → E →L[ℂ] F) (v : Fin n → E) (w : ∀ i, Fin m → E)
    (hvmem : ∀ i j, v j ∈ (S i)ᗮ)
    (hvnorm : ∀ j, ‖v j‖ = 1)
    (hwmem : ∀ i k, w i k ∈ S i)
    (hwnorm : ∀ i k, ‖w i k‖ = 1)
    (hoff : Tendsto (fun i => ‖channelOffDiagonalGram (S i) (L i)‖) l (𝓝 0)) :
    Tendsto (fun i => finiteLeakageCrossGram (L i) v (w i)) l
      (𝓝 (0 : Matrix (Fin n) (Fin m) ℂ)) := by
  apply finiteMatrix_tendsto_of_tendsto_entries
  intro j k
  change Tendsto (fun i => inner ℂ (L i (v j)) (L i (w i k))) l (𝓝 0)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_zero] using (show
    Tendsto (fun i => ‖inner ℂ (L i (v j)) (L i (w i k)) - 0‖) l (𝓝 0) by
      refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hoff
      have hid := inner_channelOffDiagonalGram_of_mem_orthogonal
        (S i) (L i) (hvmem i j) (hwmem i k)
      calc
        ‖inner ℂ (L i (v j)) (L i (w i k)) - 0‖ =
            ‖inner ℂ (L i (w i k)) (L i (v j))‖ := by
          rw [sub_zero, norm_inner_symm]
        _ = ‖inner ℂ (channelOffDiagonalGram (S i) (L i) (w i k)) (v j)‖ :=
          congrArg norm hid.symm
        _ ≤ ‖channelOffDiagonalGram (S i) (L i) (w i k)‖ * ‖v j‖ :=
          norm_inner_le_norm _ _
        _ ≤ (‖channelOffDiagonalGram (S i) (L i)‖ * ‖w i k‖) * ‖v j‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
        _ = ‖channelOffDiagonalGram (S i) (L i)‖ := by
          rw [hwnorm i k, hvnorm j]
          ring)

/-- Exact finite theorem-C assembly: persistent convergence plus the operator estimates `(11)`
and `(12)` force the full Gram limit `A₀ ⊕ I_m`. -/
theorem tendsto_finiteLeakageSplitGram_peeling
    {n m : ℕ} {ι : Type*} {l : Filter ι}
    (S : ι → Submodule ℂ E) [∀ i, (S i).HasOrthogonalProjection]
    (L : ι → E →L[ℂ] F) (v : Fin n → E) (w : ∀ i, Fin m → E)
    (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (hA : Tendsto (fun i => finiteLeakagePersistentGram (L i) v) l (𝓝 A₀))
    (hvmem : ∀ i j, v j ∈ (S i)ᗮ)
    (hvnorm : ∀ j, ‖v j‖ = 1)
    (hwmem : ∀ i k, w i k ∈ S i)
    (hwnorm : ∀ i k, ‖w i k‖ = 1)
    (hwinner : ∀ i j k, inner ℂ (w i j) (w i k) =
      (1 : Matrix (Fin m) (Fin m) ℂ) j k)
    (hdef : Tendsto (fun i => ‖channelGramDefect (S i) (L i)‖) l (𝓝 0))
    (hoff : Tendsto (fun i => ‖channelOffDiagonalGram (S i) (L i)‖) l (𝓝 0)) :
    Tendsto (fun i => finiteLeakageSplitGram (L i) v (w i)) l
      (𝓝 (finiteBlockSum A₀ (1 : Matrix (Fin m) (Fin m) ℂ))) := by
  exact tendsto_finiteHermitianBlock_peeling hA
    (tendsto_finiteLeakageCrossGram_zero_of_channelOffDiagonal
      S L v w hvmem hvnorm hwmem hwnorm hoff)
    (tendsto_finiteLeakageCrossingGram_one_of_channelDefect
      S L w hwmem hwnorm hwinner hdef)

/-- Exact squared Hilbert--Schmidt jump of the assembled finite leakage Gram is `m`. -/
theorem tendsto_trace_finiteLeakageSplitGram_peeling
    {n m : ℕ} {ι : Type*} {l : Filter ι}
    (S : ι → Submodule ℂ E) [∀ i, (S i).HasOrthogonalProjection]
    (L : ι → E →L[ℂ] F) (v : Fin n → E) (w : ∀ i, Fin m → E)
    (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (hA : Tendsto (fun i => finiteLeakagePersistentGram (L i) v) l (𝓝 A₀))
    (hvmem : ∀ i j, v j ∈ (S i)ᗮ)
    (hvnorm : ∀ j, ‖v j‖ = 1)
    (hwmem : ∀ i k, w i k ∈ S i)
    (hwnorm : ∀ i k, ‖w i k‖ = 1)
    (hwinner : ∀ i j k, inner ℂ (w i j) (w i k) =
      (1 : Matrix (Fin m) (Fin m) ℂ) j k)
    (hdef : Tendsto (fun i => ‖channelGramDefect (S i) (L i)‖) l (𝓝 0))
    (hoff : Tendsto (fun i => ‖channelOffDiagonalGram (S i) (L i)‖) l (𝓝 0)) :
    Tendsto (fun i => (finiteLeakageSplitGram (L i) v (w i)).trace - A₀.trace)
      l (𝓝 m) := by
  exact tendsto_trace_finiteGram_peeling _ A₀
    (tendsto_finiteLeakageSplitGram_peeling
      S L v w A₀ hA hvmem hvnorm hwmem hwnorm hwinner hdef hoff)

/-- Exact spectral multiset at the peeling limit: persistent roots plus `m` unit roots. -/
theorem roots_charpoly_finiteLeakageSplitGram_peeling_limit
    {n m : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℂ) :
    (finiteBlockSum A₀ (1 : Matrix (Fin m) (Fin m) ℂ)).charpoly.roots =
      A₀.charpoly.roots + Multiset.replicate m 1 :=
  roots_charpoly_finiteBlockSum_one A₀

/-! ## Layer-dependent leakage codomains

The literal shifted-Xi leakage at layer `i` lands in the model space of that layer.  The
finite Gram argument only compares scalar inner products, so its target Hilbert space may vary
with `i`.  These dependent-codomain forms retain the exact model-space targets. -/

theorem tendsto_finiteLeakageCrossingGram_one_of_channelDefect_pi
    {m : ℕ} {ι : Type*} {l : Filter ι}
    (F : ι → Type*) [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℂ (F i)] [∀ i, CompleteSpace (F i)]
    (S : ι → Submodule ℂ E) [∀ i, (S i).HasOrthogonalProjection]
    (L : ∀ i, E →L[ℂ] F i) (w : ∀ i, Fin m → E)
    (hwmem : ∀ i j, w i j ∈ S i)
    (hwnorm : ∀ i j, ‖w i j‖ = 1)
    (hwinner : ∀ i j k, inner ℂ (w i j) (w i k) =
      (1 : Matrix (Fin m) (Fin m) ℂ) j k)
    (hdef : Tendsto (fun i => ‖channelGramDefect (S i) (L i)‖) l (𝓝 0)) :
    Tendsto (fun i => finiteLeakageCrossingGram (L i) (w i)) l
      (𝓝 (1 : Matrix (Fin m) (Fin m) ℂ)) := by
  apply finiteMatrix_tendsto_of_tendsto_entries
  intro j k
  change Tendsto (fun i => inner ℂ (L i (w i j)) (L i (w i k))) l
    (𝓝 ((1 : Matrix (Fin m) (Fin m) ℂ) j k))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hdef
  have hid := inner_channelGramDefect_of_mem (S i) (L i)
    (hwmem i j) (hwmem i k)
  have heq : inner ℂ (L i (w i j)) (L i (w i k)) -
      (1 : Matrix (Fin m) (Fin m) ℂ) j k =
        inner ℂ (channelGramDefect (S i) (L i) (w i j)) (w i k) := by
    rw [← hwinner i j k]
    exact hid.symm
  rw [heq]
  calc
    ‖inner ℂ (channelGramDefect (S i) (L i) (w i j)) (w i k)‖ ≤
        ‖channelGramDefect (S i) (L i) (w i j)‖ * ‖w i k‖ :=
      norm_inner_le_norm _ _
    _ ≤ (‖channelGramDefect (S i) (L i)‖ * ‖w i j‖) * ‖w i k‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖channelGramDefect (S i) (L i)‖ := by
      rw [hwnorm i j, hwnorm i k]
      ring

theorem tendsto_finiteLeakageCrossGram_zero_of_channelOffDiagonal_pi
    {n m : ℕ} {ι : Type*} {l : Filter ι}
    (F : ι → Type*) [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℂ (F i)] [∀ i, CompleteSpace (F i)]
    (S : ι → Submodule ℂ E) [∀ i, (S i).HasOrthogonalProjection]
    (L : ∀ i, E →L[ℂ] F i) (v : Fin n → E) (w : ∀ i, Fin m → E)
    (hvmem : ∀ i j, v j ∈ (S i)ᗮ)
    (hvnorm : ∀ j, ‖v j‖ = 1)
    (hwmem : ∀ i k, w i k ∈ S i)
    (hwnorm : ∀ i k, ‖w i k‖ = 1)
    (hoff : Tendsto (fun i => ‖channelOffDiagonalGram (S i) (L i)‖) l (𝓝 0)) :
    Tendsto (fun i => finiteLeakageCrossGram (L i) v (w i)) l
      (𝓝 (0 : Matrix (Fin n) (Fin m) ℂ)) := by
  apply finiteMatrix_tendsto_of_tendsto_entries
  intro j k
  change Tendsto (fun i => inner ℂ (L i (v j)) (L i (w i k))) l (𝓝 0)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_zero] using (show
    Tendsto (fun i => ‖inner ℂ (L i (v j)) (L i (w i k)) - 0‖) l (𝓝 0) by
      refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hoff
      have hid := inner_channelOffDiagonalGram_of_mem_orthogonal
        (S i) (L i) (hvmem i j) (hwmem i k)
      calc
        ‖inner ℂ (L i (v j)) (L i (w i k)) - 0‖ =
            ‖inner ℂ (L i (w i k)) (L i (v j))‖ := by
          rw [sub_zero, norm_inner_symm]
        _ = ‖inner ℂ (channelOffDiagonalGram (S i) (L i) (w i k)) (v j)‖ :=
          congrArg norm hid.symm
        _ ≤ ‖channelOffDiagonalGram (S i) (L i) (w i k)‖ * ‖v j‖ :=
          norm_inner_le_norm _ _
        _ ≤ (‖channelOffDiagonalGram (S i) (L i)‖ * ‖w i k‖) * ‖v j‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
        _ = ‖channelOffDiagonalGram (S i) (L i)‖ := by
          rw [hwnorm i k, hvnorm j]
          ring)

/-- Exact theorem-C assembly with the literal layer-dependent model-space codomain. -/
theorem tendsto_finiteLeakageSplitGram_peeling_pi
    {n m : ℕ} {ι : Type*} {l : Filter ι}
    (F : ι → Type*) [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℂ (F i)] [∀ i, CompleteSpace (F i)]
    (S : ι → Submodule ℂ E) [∀ i, (S i).HasOrthogonalProjection]
    (L : ∀ i, E →L[ℂ] F i) (v : Fin n → E) (w : ∀ i, Fin m → E)
    (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (hA : Tendsto (fun i => finiteLeakagePersistentGram (L i) v) l (𝓝 A₀))
    (hvmem : ∀ i j, v j ∈ (S i)ᗮ)
    (hvnorm : ∀ j, ‖v j‖ = 1)
    (hwmem : ∀ i k, w i k ∈ S i)
    (hwnorm : ∀ i k, ‖w i k‖ = 1)
    (hwinner : ∀ i j k, inner ℂ (w i j) (w i k) =
      (1 : Matrix (Fin m) (Fin m) ℂ) j k)
    (hdef : Tendsto (fun i => ‖channelGramDefect (S i) (L i)‖) l (𝓝 0))
    (hoff : Tendsto (fun i => ‖channelOffDiagonalGram (S i) (L i)‖) l (𝓝 0)) :
    Tendsto (fun i => finiteLeakageSplitGram (L i) v (w i)) l
      (𝓝 (finiteBlockSum A₀ (1 : Matrix (Fin m) (Fin m) ℂ))) := by
  exact tendsto_finiteHermitianBlock_peeling hA
    (tendsto_finiteLeakageCrossGram_zero_of_channelOffDiagonal_pi
      F S L v w hvmem hvnorm hwmem hwnorm hoff)
    (tendsto_finiteLeakageCrossingGram_one_of_channelDefect_pi
      F S L w hwmem hwnorm hwinner hdef)

/-- Exact squared Hilbert--Schmidt jump for a layer-dependent leakage codomain. -/
theorem tendsto_trace_finiteLeakageSplitGram_peeling_pi
    {n m : ℕ} {ι : Type*} {l : Filter ι}
    (F : ι → Type*) [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℂ (F i)] [∀ i, CompleteSpace (F i)]
    (S : ι → Submodule ℂ E) [∀ i, (S i).HasOrthogonalProjection]
    (L : ∀ i, E →L[ℂ] F i) (v : Fin n → E) (w : ∀ i, Fin m → E)
    (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (hA : Tendsto (fun i => finiteLeakagePersistentGram (L i) v) l (𝓝 A₀))
    (hvmem : ∀ i j, v j ∈ (S i)ᗮ)
    (hvnorm : ∀ j, ‖v j‖ = 1)
    (hwmem : ∀ i k, w i k ∈ S i)
    (hwnorm : ∀ i k, ‖w i k‖ = 1)
    (hwinner : ∀ i j k, inner ℂ (w i j) (w i k) =
      (1 : Matrix (Fin m) (Fin m) ℂ) j k)
    (hdef : Tendsto (fun i => ‖channelGramDefect (S i) (L i)‖) l (𝓝 0))
    (hoff : Tendsto (fun i => ‖channelOffDiagonalGram (S i) (L i)‖) l (𝓝 0)) :
    Tendsto (fun i => (finiteLeakageSplitGram (L i) v (w i)).trace - A₀.trace)
      l (𝓝 m) := by
  exact tendsto_trace_finiteGram_peeling _ A₀
    (tendsto_finiteLeakageSplitGram_peeling_pi
      F S L v w A₀ hA hvmem hvnorm hwmem hwnorm hwinner hdef hoff)

end

end GaloisForLFunctions.HTGeometry
