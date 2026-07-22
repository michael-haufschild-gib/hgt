import GaloisForLFunctions.HTGeometry.FiniteFieldStateSpaceHankelRank
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn
import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# Fixed modal width is not compact-open dense in a hypertranscendental function

A family of entire functions whose derivative sequence at every point has modal width at most
`d` has a singular `(d + 1) × (d + 1)` derivative Hankel matrix.  Compact-open convergence
transports every derivative, so the same determinant vanishes identically for the limit.

That determinant is a nonzero differential polynomial: its nonzeroness is certified by evaluating
it on any `d + 1`-line packet with distinct nodes and nonzero weights.  Consequently no
hypertranscendental function lies in the locally-uniform closure of a uniformly bounded modal
family.  This is a nonlinear closure law; frequencies and amplitudes may vary arbitrarily and
need not converge.
-/

open Complex Filter Topology
open scoped BigOperators Matrix

namespace HTGeometry

noncomputable section

open GaloisForLFunctions

/-- Modal width is monotone: an additional zero-amplitude line pads every presentation. -/
theorem FiniteModalWidthAtMost.succ {d : ℕ} {m : ℕ → ℂ}
    (h : FiniteModalWidthAtMost d m) :
    FiniteModalWidthAtMost (d + 1) m := by
  obtain ⟨weight, node, rfl⟩ := h
  refine ⟨Fin.cases 0 weight, Fin.cases 0 node, ?_⟩
  funext n
  simp [finiteModalSequence, Fin.sum_univ_succ]

/-- Any finite modal presentation can be padded to a larger prescribed width. -/
theorem FiniteModalWidthAtMost.mono {d e : ℕ} {m : ℕ → ℂ}
    (h : FiniteModalWidthAtMost d m) (hde : d ≤ e) :
    FiniteModalWidthAtMost e m := by
  exact Nat.le_induction h (fun _ _ hk => hk.succ) e hde

/-- Universal differential-Hankel polynomial of modal width `d`.  Variable zero is reserved for
the base point; the entry `(i,j)` is the derivative variable of order `i+j`. -/
def derivativeHankelPolynomial (d : ℕ) : MvPolynomial (Fin (2 * d + 2)) ℂ :=
  (Matrix.of fun i j : Fin (d + 1) =>
    MvPolynomial.X (Fin.succ ⟨(i : ℕ) + (j : ℕ), by omega⟩)).det

/-- Evaluation of the universal polynomial is the derivative-Hankel determinant. -/
theorem eval_derivativeHankelPolynomial (d : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    MvPolynomial.eval
        (Fin.cons z fun k : Fin (2 * d + 1) => iteratedDeriv (k : ℕ) f z)
        (derivativeHankelPolynomial d) =
      (algebraicHankelMatrix (fun k => iteratedDeriv k f z) (d + 1)).det := by
  rw [derivativeHankelPolynomial, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply]
  change MvPolynomial.eval
      (Fin.cons z fun k : Fin (2 * d + 1) => iteratedDeriv (k : ℕ) f z)
      (MvPolynomial.X (Fin.succ
        (⟨(i : ℕ) + (j : ℕ), by omega⟩ : Fin (2 * d + 1)))) = _
  rw [MvPolynomial.eval_X]
  let jet : Fin (2 * d + 1) → ℂ := fun k => iteratedDeriv (k : ℕ) f z
  change (Fin.cons z jet : Fin (2 * d + 2) → ℂ)
      (Fin.succ (⟨(i : ℕ) + (j : ℕ), by omega⟩ : Fin (2 * d + 1))) = _
  rw [Fin.cons_succ]
  rfl

/-- The universal derivative-Hankel determinant is a genuine, nonzero differential polynomial. -/
theorem derivativeHankelPolynomial_ne_zero (d : ℕ) :
    derivativeHankelPolynomial d ≠ 0 := by
  let node : Fin (d + 1) → ℂ := fun i => (i : ℂ)
  let weight : Fin (d + 1) → ℂ := fun _ => 1
  let moment : ℕ → ℂ := finiteModalSequence weight node
  let y : Fin (2 * d + 2) → ℂ :=
    Fin.cases 0 (fun k => moment (k : ℕ))
  have hnode : Function.Injective node := by
    intro i j hij
    apply Fin.ext
    dsimp [node] at hij
    exact_mod_cast hij
  have hdet : (algebraicHankelMatrix moment (d + 1)).det ≠ 0 :=
    det_algebraicHankelMatrix_finiteModalSequence_ne_zero hnode (fun _ => one_ne_zero)
  intro hzero
  apply hdet
  have heval : MvPolynomial.eval y (derivativeHankelPolynomial d) =
      (algebraicHankelMatrix moment (d + 1)).det := by
    rw [derivativeHankelPolynomial, RingHom.map_det]
    congr 1
    ext i j
    simp [y, moment, algebraicHankelMatrix]
  rw [hzero, map_zero] at heval
  exact heval.symm

/-- Identical derivative-Hankel rank loss is an algebraic differential equation. -/
theorem differentiallyAlgebraic_of_forall_derivativeHankel_det_eq_zero
    {f : ℂ → ℂ} {d : ℕ}
    (hdet : ∀ z : ℂ,
      (algebraicHankelMatrix (fun k => iteratedDeriv k f z) (d + 1)).det = 0) :
    DifferentiallyAlgebraic f := by
  refine ⟨2 * d, derivativeHankelPolynomial d,
    derivativeHankelPolynomial_ne_zero d, ?_⟩
  intro z
  rw [eval_derivativeHankelPolynomial]
  exact hdet z

/-- A hypertranscendental function has some point where every prescribed finite derivative-Hankel
block is nonsingular. -/
theorem exists_derivativeHankel_det_ne_zero_of_hypertranscendental
    {f : ℂ → ℂ} (hf : Hypertranscendental f) (d : ℕ) :
    ∃ z : ℂ,
      (algebraicHankelMatrix (fun k => iteratedDeriv k f z) (d + 1)).det ≠ 0 := by
  by_contra h
  push Not at h
  exact hf (differentiallyAlgebraic_of_forall_derivativeHankel_det_eq_zero h)

/-- **Fixed-modal compact-open exclusion law.**  Frequencies and amplitudes may vary with `n` and
with the observation point.  Uniform modal width alone prevents locally-uniform convergence to a
hypertranscendental target. -/
theorem not_tendstoLocallyUniformly_of_hypertranscendental_of_fixedModalJetWidth
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {d : ℕ}
    (hF : ∀ n, Differentiable ℂ (F n))
    (hf : Hypertranscendental f)
    (hwidth : ∀ᶠ n in atTop, ∀ z,
      FiniteModalWidthAtMost d (fun k => iteratedDeriv k (F n) z)) :
    ¬ TendstoLocallyUniformly F f atTop := by
  intro hconv
  obtain ⟨z, hz⟩ := exists_derivativeHankel_det_ne_zero_of_hypertranscendental hf d
  let m : ℕ → ℕ → ℂ := fun n k => iteratedDeriv k (F n) z
  let target : ℕ → ℂ := fun k => iteratedDeriv k f z
  have hm : ∀ᶠ n in atTop, AlgebraicStateSpaceDimensionAtMost d (m n) :=
    hwidth.mono fun n hn =>
      algebraicStateSpaceDimensionAtMost_of_finiteModalWidthAtMost (hn z)
  have hjet : Tendsto m atTop (nhds target) := by
    apply tendsto_pi_nhds.mpr
    intro k
    exact iteratedDeriv_tendsto_of_locallyUniform isOpen_univ
      (tendstoLocallyUniformlyOn_univ.mpr hconv)
      (Filter.Eventually.of_forall fun n => (hF n).differentiableOn)
      k (Set.mem_univ z)
  have hmatrix : Tendsto
      (fun n => algebraicHankelMatrix (m n) (d + 1)) atTop
      (nhds (algebraicHankelMatrix target (d + 1))) := by
    apply tendsto_pi_nhds.mpr
    intro r
    apply tendsto_pi_nhds.mpr
    intro c
    simpa [algebraicHankelMatrix] using
      (tendsto_pi_nhds.mp hjet) ((r : ℕ) + (c : ℕ))
  have hdet : Tendsto
      (fun n => (algebraicHankelMatrix (m n) (d + 1)).det) atTop
      (nhds (algebraicHankelMatrix target (d + 1)).det) :=
    continuous_id.matrix_det.continuousAt.tendsto.comp hmatrix
  have hzero : Tendsto
      (fun n => (algebraicHankelMatrix (m n) (d + 1)).det) atTop (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    exact hm.mono fun n hn =>
      (det_algebraicHankelMatrix_succ_eq_zero_of_stateSpaceDimensionAtMost hn).symm
  exact hz (tendsto_nhds_unique hdet hzero)

end

end HTGeometry
