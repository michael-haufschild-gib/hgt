/-
# The sorted spectrum is real-analytic where it is simple

The canonical increasing labelling of the spectrum is continuous everywhere and, where the spectrum
is simple, coincides locally with the analytic eigenvalue branches: each branch value is a root of
the characteristic relation, hence one of the eigenvalues, and the eigenvalues are separated at the
base point, so the branch cannot jump between them.  Restricting a holomorphic branch to real
coefficients and taking the real part is real-analytic, so the sorted spectrum -- and every linear
functional of it, in particular a spectral action -- is real-analytic on the simple locus.

Main results:
* `exists_eigenvalue_eq_of_charpolyDet_eq_zero` — a root of the characteristic relation of a
  Hermitian matrix is one of its eigenvalues.
* `realEmbed`, `analyticAt_re_comp_realEmbed` — the real restriction of a holomorphic function.
* `exists_analyticBranches_spectralEnsemble` — analytic branches of the ensemble at a simple point.
* `analyticAt_sortedTuple_eigenvalues` — **the sorted spectrum is real-analytic at a simple
  point**.
* `analyticAt_sortedSpectralAction` — **hence so is the spectral action**.
-/
import GaloisForLFunctions.HTGeometry.SpectralActionPhase
import GaloisForLFunctions.HTGeometry.SubmoduleEndpointGenericity
import GaloisForLFunctions.HTGeometry.RootPacketRelabelling

open Filter Topology Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- A root of the characteristic relation of a Hermitian matrix is one of its eigenvalues. -/
theorem exists_eigenvalue_eq_of_charpolyDet_eq_zero {I : Type*} [Fintype I] [DecidableEq I]
    {M : Matrix I I ℂ} (hM : M.IsHermitian) {z : ℂ}
    (hz : (Matrix.scalar I z - M).det = 0) : ∃ i, z = ((hM.eigenvalues i : ℝ) : ℂ) := by
  have heval : M.charpoly.IsRoot z := by
    show Polynomial.eval z M.charpoly = 0
    rw [Matrix.eval_charpoly]
    exact hz
  have hroot : z ∈ M.charpoly.roots :=
    (Polynomial.mem_roots (M.charpoly_monic).ne_zero).mpr heval
  rw [← hermitianEigenvalues_rootMultiset hM] at hroot
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hroot
  exact ⟨i, hi.symm⟩

/-- The real coefficient vectors inside the complex ones. -/
def realEmbed (q : Fin N → ℝ) : Fin N → ℂ := fun a => ((q a : ℝ) : ℂ)

/-- The embedding as a continuous real-linear map. -/
def realEmbedCLM (N : ℕ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℂ) :=
  ContinuousLinearMap.pi fun a => Complex.ofRealCLM.comp (ContinuousLinearMap.proj a)

theorem realEmbedCLM_apply (q : Fin N → ℝ) : realEmbedCLM N q = realEmbed q := rfl

theorem continuous_realEmbed : Continuous (realEmbed (N := N)) := (realEmbedCLM N).continuous

/-- The real restriction of a holomorphic function of the coefficients is real-analytic. -/
theorem analyticAt_re_comp_realEmbed {f : (Fin N → ℂ) → ℂ} {θ₀ : Fin N → ℝ}
    (hf : AnalyticAt ℂ f (realEmbed θ₀)) :
    AnalyticAt ℝ (fun q : Fin N → ℝ => (f (realEmbed q)).re) θ₀ := by
  have hemb : AnalyticAt ℝ (realEmbed (N := N)) θ₀ := (realEmbedCLM N).analyticAt θ₀
  have hfR : AnalyticAt ℝ f (realEmbed θ₀) := hf.restrictScalars
  have hcomp : AnalyticAt ℝ (fun q : Fin N → ℝ => f (realEmbed q)) θ₀ := hfR.comp hemb
  exact (Complex.reCLM.analyticAt _).comp hcomp

/-- **Analytic eigenvalue branches of the Hermitian ensemble at a simple point.** -/
theorem exists_analyticBranches_spectralEnsemble {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (θ₀ : Fin N → ℝ)
    (hinj : Function.Injective (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues) :
    ∃ branch : Fin D → (Fin N → ℂ) → ℂ,
      (∀ x, AnalyticAt ℂ (branch x) (realEmbed θ₀)) ∧
      (∀ x, branch x (realEmbed θ₀)
        = (((isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues x : ℝ) : ℂ)) ∧
      (∀ x, ∀ᶠ θ in 𝓝 (realEmbed θ₀),
        (Matrix.scalar (Fin D) (branch x θ) - (∑ a, θ a • P a)).det = 0) := by
  classical
  set hHerm := isHermitian_spectralEnsembleMatrix hP θ₀ with hHermDef
  have hU1 : (hHerm.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ *
      (hHerm.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    have h := Unitary.coe_star_mul_self hHerm.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose] at h
  have hbase : (hHerm.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)ᴴ *
      (∑ a, (realEmbed θ₀) a • P a) *
      (hHerm.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ)
      = Matrix.diagonal (fun i => ((hHerm.eigenvalues i : ℝ) : ℂ)) :=
    conjTranspose_mul_mul_eigenvectorUnitary hHerm
  have hinjC : Function.Injective (fun i => ((hHerm.eigenvalues i : ℝ) : ℂ)) := by
    intro i j hij
    exact hinj (Complex.ofReal_injective (by exact hij))
  choose branch hban hb0 hroot using fun x =>
    exists_analyticBranches_linearFamily P (realEmbed θ₀) hU1
      (fun i => ((hHerm.eigenvalues i : ℝ) : ℂ)) hinjC hbase x
  exact ⟨branch, hban, hb0, hroot⟩

section Simple

variable {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

/-- The canonically labelled spectrum of the ensemble. -/
def sortedEnsembleSpectrum (hP : ∀ a, (P a).IsHermitian) (θ : Fin N → ℝ) : Fin D → ℝ :=
  sortedTuple (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues

theorem continuous_sortedEnsembleSpectrum (hP : ∀ a, (P a).IsHermitian) :
    Continuous (sortedEnsembleSpectrum hP) :=
  continuous_sortedTuple_eigenvalues (continuous_spectralEnsembleMatrix P)
    (fun θ => isHermitian_spectralEnsembleMatrix hP θ)

theorem injective_sortedTuple {a : Fin D → ℝ} (ha : Function.Injective a) :
    Function.Injective (sortedTuple a) :=
  ha.comp (Tuple.sort a).injective

theorem exists_sortedTuple_eq (a : Fin D → ℝ) (i : Fin D) : ∃ j, a i = sortedTuple a j :=
  ⟨(Tuple.sort a).symm i, by
    show a i = a (Tuple.sort a ((Tuple.sort a).symm i))
    rw [Equiv.apply_symm_apply]⟩

theorem sortedTuple_symm_apply (a : Fin D → ℝ) (x : Fin D) :
    sortedTuple a ((Tuple.sort a).symm x) = a x := by
  show a (Tuple.sort a ((Tuple.sort a).symm x)) = a x
  rw [Equiv.apply_symm_apply]

/-- **The sorted spectrum is real-analytic at a point of simple spectrum.** -/
theorem analyticAt_sortedEnsembleSpectrum (hP : ∀ a, (P a).IsHermitian) {θ₀ : Fin N → ℝ}
    (hinj : Function.Injective (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues)
    (j : Fin D) :
    AnalyticAt ℝ (fun q : Fin N → ℝ => sortedEnsembleSpectrum hP q j) θ₀ := by
  classical
  obtain ⟨branch, hban, hb0, hroot⟩ := exists_analyticBranches_spectralEnsemble hP θ₀ hinj
  set σ := Tuple.sort (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues with hσ
  set x : Fin D := σ j with hx
  set f : (Fin N → ℝ) → ℝ := fun q => (branch x (realEmbed q)).re with hf
  have hfana : AnalyticAt ℝ f θ₀ := analyticAt_re_comp_realEmbed (hban x)
  have hSinj : Function.Injective (sortedEnsembleSpectrum hP θ₀) := injective_sortedTuple hinj
  have hfθ₀ : f θ₀ = sortedEnsembleSpectrum hP θ₀ j := by
    rw [hf]
    show (branch x (realEmbed θ₀)).re = _
    rw [hb0 x]
    show (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues x = _
    rw [hx, hσ]
    rfl
  -- the branch value is always one of the eigenvalues
  have hmem : ∀ᶠ q in 𝓝 θ₀, ∃ i : Fin D, f q = sortedEnsembleSpectrum hP q i := by
    have hpull : ∀ᶠ q in 𝓝 θ₀,
        (Matrix.scalar (Fin D) (branch x (realEmbed q)) - (∑ a, (realEmbed q) a • P a)).det = 0 :=
      (continuous_realEmbed.tendsto θ₀).eventually (hroot x)
    filter_upwards [hpull] with q hq
    have hHq : (∑ a, (realEmbed q) a • P a) = spectralEnsembleMatrix P q := rfl
    rw [hHq] at hq
    obtain ⟨i, hi⟩ := exists_eigenvalue_eq_of_charpolyDet_eq_zero
      (isHermitian_spectralEnsembleMatrix hP q) hq
    obtain ⟨j', hj'⟩ := exists_sortedTuple_eq
      (isHermitian_spectralEnsembleMatrix hP q).eigenvalues i
    refine ⟨j', ?_⟩
    rw [hf]
    show (branch x (realEmbed q)).re = _
    rw [hi]
    show (isHermitian_spectralEnsembleMatrix hP q).eigenvalues i = _
    exact hj'
  -- separation: no other sorted coordinate can equal the branch near the base point
  have hsep : ∀ i : Fin D, i ≠ j →
      ∀ᶠ q in 𝓝 θ₀, sortedEnsembleSpectrum hP q i ≠ f q := by
    intro i hi
    set c : ℝ := |sortedEnsembleSpectrum hP θ₀ i - sortedEnsembleSpectrum hP θ₀ j| with hc
    have hcpos : 0 < c := abs_pos.mpr (sub_ne_zero.mpr fun h => hi (hSinj h))
    have h1 : ∀ᶠ q in 𝓝 θ₀,
        |sortedEnsembleSpectrum hP q i - sortedEnsembleSpectrum hP θ₀ i| < c / 2 := by
      have hcont : ContinuousAt (fun q => sortedEnsembleSpectrum hP q i) θ₀ :=
        ((continuous_apply i).comp (continuous_sortedEnsembleSpectrum hP)).continuousAt
      have := hcont (Metric.ball_mem_nhds (sortedEnsembleSpectrum hP θ₀ i) (half_pos hcpos))
      filter_upwards [this] with q hq
      simpa [Real.dist_eq] using hq
    have h2 : ∀ᶠ q in 𝓝 θ₀, |f q - sortedEnsembleSpectrum hP θ₀ j| < c / 2 := by
      have hcont : ContinuousAt f θ₀ := hfana.continuousAt
      have := hcont (Metric.ball_mem_nhds (f θ₀) (half_pos hcpos))
      filter_upwards [this] with q hq
      rw [← hfθ₀]
      simpa [Real.dist_eq] using hq
    filter_upwards [h1, h2] with q hq1 hq2 heq
    have hchain : c ≤ |sortedEnsembleSpectrum hP θ₀ i - sortedEnsembleSpectrum hP q i|
        + |sortedEnsembleSpectrum hP q i - sortedEnsembleSpectrum hP θ₀ j| :=
      abs_sub_le _ _ _
    rw [heq] at hchain
    rw [abs_sub_comm, heq] at hq1
    linarith [hchain, hq1, hq2]
  have hall : ∀ᶠ q in 𝓝 θ₀, ∀ i : Fin D, i ≠ j → sortedEnsembleSpectrum hP q i ≠ f q := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i = j
    · subst hi
      exact Filter.Eventually.of_forall fun q h => absurd rfl h
    · filter_upwards [hsep i hi] with q hq
      intro _
      exact hq
  have hfinal : ∀ᶠ q in 𝓝 θ₀, f q = sortedEnsembleSpectrum hP q j := by
    filter_upwards [hmem, hall] with q hq1 hq2
    obtain ⟨i, hi⟩ := hq1
    by_cases hij : i = j
    · rw [hi, hij]
    · exact absurd hi.symm (hq2 i hij)
  exact hfana.congr hfinal

/-- **The canonically labelled spectral action is real-analytic at a point of simple spectrum.** -/
theorem analyticAt_sortedSpectralAction (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ)
    {θ₀ : Fin N → ℝ}
    (hinj : Function.Injective (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues) :
    AnalyticAt ℝ (sortedSpectralAction hP k) θ₀ := by
  refine Finset.analyticAt_fun_sum _ fun j _ => ?_
  exact analyticAt_const.mul (analyticAt_sortedEnsembleSpectrum hP hinj j)

end Simple

end

end GaloisForLFunctions.HTGeometry
