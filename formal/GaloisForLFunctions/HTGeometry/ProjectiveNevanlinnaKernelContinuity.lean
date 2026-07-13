import GaloisForLFunctions.HTGeometry.ProjectiveCauchyKernelContinuity
import GaloisForLFunctions.HTGeometry.ProjectiveNevanlinnaGenericity

/-!
# Operator-norm continuity of projective Nevanlinna-jet controls

The genuine Nevanlinna jet kernel is treated as its finite forward triangular expansion in
projective Cauchy powers.  This removes an unnecessary inverse-matrix continuity problem:
nonvanishing of the triangular diagonal is needed for controllability, but not for continuity.

On a collar `Im(q z) ≥ η > 0`, smoothness of `a` and `q` makes every recursive jet coefficient
continuous in `z`, while the projective Cauchy powers vary continuously in the sup norm.  The
whole genuine jet packet consequently varies continuously in `L¹`, and its `L∞` density-control
operator varies continuously in operator norm.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Topology
open scoped ENNReal OnePoint

noncomputable section

/-- Source nodes whose projective image has a fixed positive imaginary lower bound. -/
abbrev NevanlinnaUpperNodeAtLeast (q : ℂ → ℂ) (η : ℝ) :=
  {z : ℂ // η ≤ (q z).im}

/-- A source node on a Nevanlinna upper collar, viewed as its upper-half-plane projective image. -/
def nevanlinnaUpperNodeImage (q : ℂ → ℂ) (η : ℝ)
    (z : NevanlinnaUpperNodeAtLeast q η) : UpperNodeAtLeast η :=
  ⟨q z.1, z.2⟩

theorem continuous_nevanlinnaUpperNodeImage
    {q : ℂ → ℂ} {η : ℝ} (hq : Continuous q) :
    Continuous (nevanlinnaUpperNodeImage q η) := by
  simpa only [nevanlinnaUpperNodeImage] using
    (hq.comp continuous_subtype_val).subtype_mk (fun z => z.2)

/-- The forward triangular projective Nevanlinna-jet expansion.  It is defined without any
regularity assumption on the diagonal. -/
def projectiveNevanlinnaJetExpansionColumn
    {ι : Type*} (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (t : OnePoint ℝ) : ((Σ i, Fin (n i)) → ℂ) :=
  fun s => ∑ k : Fin (n s.1),
    nevanlinnaJetCoeff a q s.2 k (z s.1) *
      projectiveCauchyPower (q (z s.1)) k t

/-- At a fixed source packet in an upper collar, the forward Nevanlinna expansion is continuous
on the entire projective parameter line. -/
theorem continuous_projectiveNevanlinnaJetExpansionColumn
    {ι : Type*} [Fintype ι]
    {a q : ℂ → ℂ}
    (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (z : ι → NevanlinnaUpperNodeAtLeast q η) :
    Continuous (projectiveNevanlinnaJetExpansionColumn
      a q (fun i => (z i).1) n) := by
  apply continuous_pi
  intro s
  exact continuous_finsetSum Finset.univ fun k _ =>
    continuous_const.mul
      (continuous_projectiveCauchyPower (q (z s.1).1)
        (ne_of_gt (hη.trans_le (z s.1).2)) k)

/-- The genuine forward jet packet as one continuous vector-valued function on the projective
parameter line. -/
def projectiveNevanlinnaJetExpansionContinuousMap
    {ι : Type*} [Fintype ι]
    {a q : ℂ → ℂ}
    (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (z : ι → NevanlinnaUpperNodeAtLeast q η) :
    C(OnePoint ℝ, (Σ i, Fin (n i)) → ℂ) :=
  ⟨projectiveNevanlinnaJetExpansionColumn a q (fun i => (z i).1) n,
    continuous_projectiveNevanlinnaJetExpansionColumn η hη n z⟩

@[simp]
theorem projectiveNevanlinnaJetExpansionContinuousMap_apply
    {ι : Type*} [Fintype ι]
    {a q : ℂ → ℂ}
    (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (z : ι → NevanlinnaUpperNodeAtLeast q η) (t : OnePoint ℝ) :
    projectiveNevanlinnaJetExpansionContinuousMap (a := a) (q := q) η hη n z t =
      projectiveNevanlinnaJetExpansionColumn a q (fun i => (z i).1) n t :=
  rfl

/-- The complete forward Nevanlinna jet packet varies continuously in the projective sup norm
with all source nodes on a common upper collar. -/
theorem continuous_projectiveNevanlinnaJetExpansionContinuousMap
    {ι : Type*} [Fintype ι]
    {a q : ℂ → ℂ} (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (η : ℝ) (hη : 0 < η) (n : ι → ℕ) :
    Continuous (projectiveNevanlinnaJetExpansionContinuousMap
      (a := a) (q := q) η hη n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply continuous_pi
  intro s
  change Continuous (fun p :
      (ι → NevanlinnaUpperNodeAtLeast q η) × OnePoint ℝ =>
    ∑ k : Fin (n s.1), nevanlinnaJetCoeff a q s.2 k (p.1 s.1).1 *
      projectiveCauchyPower (q (p.1 s.1).1) k p.2)
  exact continuous_finsetSum (Finset.univ : Finset (Fin (n s.1))) fun k _ => by
    have hz : Continuous
        (fun p : (ι → NevanlinnaUpperNodeAtLeast q η) × OnePoint ℝ =>
          ((p.1 s.1).1 : ℂ)) := by
      fun_prop
    have hc : Continuous
        (fun p : (ι → NevanlinnaUpperNodeAtLeast q η) × OnePoint ℝ =>
          nevanlinnaJetCoeff a q s.2 k (p.1 s.1).1) :=
      (contDiff_nevanlinnaJetCoeff ha hq s.2 k).continuous.comp hz
    have hx : Continuous
        (fun p : (ι → NevanlinnaUpperNodeAtLeast q η) × OnePoint ℝ =>
          nevanlinnaUpperNodeImage q η (p.1 s.1)) :=
      (continuous_nevanlinnaUpperNodeImage hq.continuous).comp (by fun_prop)
    have hp' : Continuous
        (fun p : (ι → NevanlinnaUpperNodeAtLeast q η) × OnePoint ℝ =>
          projectiveCauchyPowerContinuousMap η hη k
            (nevanlinnaUpperNodeImage q η (p.1 s.1)) p.2) :=
      continuous_eval.comp
        (((continuous_projectiveCauchyPowerContinuousMap η hη k).comp hx).prodMk
          continuous_snd)
    have hp : Continuous
        (fun p : (ι → NevanlinnaUpperNodeAtLeast q η) × OnePoint ℝ =>
          projectiveCauchyPower (q (p.1 s.1).1) k p.2) := by
      simpa only [projectiveCauchyPowerContinuousMap_apply,
        nevanlinnaUpperNodeImage] using hp'
    exact hc.mul hp

/-- The canonical `L¹` class of the genuine forward Nevanlinna jet kernel. -/
def projectiveNevanlinnaJetExpansionLpKernel
    {ι : Type*} [Fintype ι]
    {a q : ℂ → ℂ}
    (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (z : ι → NevanlinnaUpperNodeAtLeast q η) :
    Lp ((Σ i, Fin (n i)) → ℂ) 1 mu :=
  ContinuousMap.toLp 1 mu ℝ
    (projectiveNevanlinnaJetExpansionContinuousMap (a := a) (q := q) η hη n z)

/-- Genuine forward Nevanlinna jet kernels vary continuously as `L¹` classes. -/
theorem continuous_projectiveNevanlinnaJetExpansionLpKernel
    {ι : Type*} [Fintype ι]
    {a q : ℂ → ℂ} (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] :
    Continuous (projectiveNevanlinnaJetExpansionLpKernel
      (a := a) (q := q) η hη n mu) := by
  exact (ContinuousMap.toLp 1 mu ℝ).continuous.comp
    (continuous_projectiveNevanlinnaJetExpansionContinuousMap ha hq η hη n)

/-- The forward expansion is `L¹` for every finite projective measure. -/
theorem memLp_projectiveNevanlinnaJetExpansionColumn
    {ι : Type*} [Fintype ι]
    {a q : ℂ → ℂ}
    (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (z : ι → NevanlinnaUpperNodeAtLeast q η) :
    MemLp (projectiveNevanlinnaJetExpansionColumn a q (fun i => (z i).1) n) 1 mu := by
  exact (continuous_projectiveNevanlinnaJetExpansionColumn η hη n z)
    |>.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The continuous-function `L¹` class is the class used by the direct Bochner control. -/
theorem projectiveNevanlinnaJetExpansionLpKernel_eq_memLpToLp
    {ι : Type*} [Fintype ι]
    {a q : ℂ → ℂ}
    (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (z : ι → NevanlinnaUpperNodeAtLeast q η) :
    projectiveNevanlinnaJetExpansionLpKernel (a := a) (q := q) η hη n mu z =
      (memLp_projectiveNevanlinnaJetExpansionColumn η hη n mu z).toLp
        (projectiveNevanlinnaJetExpansionColumn a q (fun i => (z i).1) n) := by
  apply Lp.ext
  exact (ContinuousMap.coeFn_toLp mu
    (projectiveNevanlinnaJetExpansionContinuousMap
      (a := a) (q := q) η hη n z)).trans
      (MemLp.coeFn_toLp _).symm

/-- **Projective Nevanlinna control continuity.** On a uniformly upper source-node packet, the
actual bounded-density control of the finite forward genuine-jet expansion varies continuously in
operator norm. -/
theorem continuous_projectiveNevanlinnaJetExpansionLinftyBochnerControl
    {ι : Type*} [Fintype ι]
    {a q : ℂ → ℂ} (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (η : ℝ) (hη : 0 < η) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] :
    Continuous (fun z : ι → NevanlinnaUpperNodeAtLeast q η =>
      linftyBochnerControl mu
        (projectiveNevanlinnaJetExpansionColumn a q (fun i => (z i).1) n)
        (memLp_projectiveNevanlinnaJetExpansionColumn η hη n mu z)) := by
  apply continuous_linftyBochnerControl_of_continuous_toLp
  have heq : (fun z : ι → NevanlinnaUpperNodeAtLeast q η =>
      (memLp_projectiveNevanlinnaJetExpansionColumn η hη n mu z).toLp
        (projectiveNevanlinnaJetExpansionColumn a q (fun i => (z i).1) n)) =
      projectiveNevanlinnaJetExpansionLpKernel
        (a := a) (q := q) η hη n mu := by
    funext z
    exact (projectiveNevanlinnaJetExpansionLpKernel_eq_memLpToLp
      η hη n mu z).symm
  rw [heq]
  exact continuous_projectiveNevanlinnaJetExpansionLpKernel ha hq η hη n mu

end

end GaloisForLFunctions.HTGeometry
