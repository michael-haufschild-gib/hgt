import GaloisForLFunctions.HTGeometry.ProjectiveCauchyKernelSmoothness
import GaloisForLFunctions.HTGeometry.ProjectiveNevanlinnaKernelContinuity
import Mathlib.Analysis.Analytic.Constructions

/-!
# Smoothness of the actual projective Nevanlinna row-evaluation family

The transversality family is not an abstract surrogate.  Its coordinates are the forward
triangular expansion of the genuine Nevanlinna jets, paired against the actual bounded density.
This module assembles the smooth projective resolvent from
`ProjectiveCauchyKernelSmoothness`, proves smoothness of the complete finite vector kernel in the
sup norm, passes through the canonical `C → L¹` map and the bounded-density pairing, and finally
identifies the result with the existing projective Nevanlinna control.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set
open scoped ENNReal OnePoint

noncomputable section

/-- Complex smoothness implies real smoothness by analytic scalar restriction. -/
theorem contDiff_real_of_contDiff_complex
    {f : ℂ → ℂ} (hf : ContDiff ℂ ⊤ f) : ContDiff ℝ ⊤ f := by
  exact hf.analyticOnNhd.restrictScalars.contDiff

/-- Complex smoothness on an open locus implies real smoothness on the same locus. -/
theorem contDiffOn_real_of_contDiffOn_complex_of_isOpen
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℂ ⊤ f U) : ContDiffOn ℝ ⊤ f U := by
  intro z hz
  have hcomplex : ContDiffAt ℂ ⊤ f z := hf.contDiffAt (hU.mem_nhds hz)
  exact hcomplex.analyticAt.restrictScalars.contDiffAt.contDiffWithinAt

/-- Recursive Nevanlinna jet coefficients are smooth on every open locus on which the input
coordinates are smooth.  No global extension across poles is required. -/
theorem contDiffOn_nevanlinnaJetCoeff_of_isOpen
    {a q : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (ha : ContDiffOn ℂ ⊤ a U) (hq : ContDiffOn ℂ ⊤ q U) :
    ∀ r k, ContDiffOn ℂ ⊤ (nevanlinnaJetCoeff a q r k) U := by
  intro r
  induction r with
  | zero =>
      intro k
      simp only [nevanlinnaJetCoeff]
      split
      · exact ha
      · exact contDiffOn_const
  | succ r ihr =>
      intro k
      simp only [nevanlinnaJetCoeff]
      apply ContDiffOn.add
      · simpa using (ihr k).deriv_of_isOpen hU (by simp)
      · split
        · exact contDiffOn_const
        · exact (contDiffOn_const.mul
            (by simpa using hq.deriv_of_isOpen hU (by simp))).mul (ihr (k - 1))

/-- Assemble finitely many scalar continuous functions into one continuous function with a finite
vector target. -/
def projectiveContinuousMapPiCLM
    {σ : Type} [Fintype σ] :
    (σ → C(OnePoint ℝ, ℂ)) →L[ℂ] C(OnePoint ℝ, σ → ℂ) :=
  ({ toFun := fun f =>
        ⟨fun t s => f s t, continuous_pi fun s => (f s).continuous⟩
     map_add' := by
       intro f g
       ext t s
       rfl
     map_smul' := by
       intro c f
       ext t s
       rfl } : (σ → C(OnePoint ℝ, ℂ)) →ₗ[ℂ] C(OnePoint ℝ, σ → ℂ)).mkContinuous 1
    (fun f => by
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
      intro t
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).2
      intro s
      exact (f s).norm_coe_le_norm t |>.trans (norm_le_pi_norm f s))

@[simp]
theorem projectiveContinuousMapPiCLM_apply
    {σ : Type} [Fintype σ]
    (f : σ → C(OnePoint ℝ, ℂ)) (t : OnePoint ℝ) (s : σ) :
    projectiveContinuousMapPiCLM f t s = f s t :=
  rfl

/-- The open locus of source-node packets whose projective images lie in the upper half-plane. -/
def nevanlinnaUpperPacketSet
    {ι : Type} (q : ℂ → ℂ) : Set (ι → ℂ) :=
  {z | ∀ i, 0 < (q (z i)).im}

/-- Upper projective packets whose source nodes also lie in a specified regularity locus. -/
def nevanlinnaUpperPacketSetWithin
    {ι : Type} (q : ℂ → ℂ) (U : Set ℂ) : Set (ι → ℂ) :=
  nevanlinnaUpperPacketSet q ∩ Set.pi Set.univ (fun _ => U)

/-- The complete forward Nevanlinna-jet kernel, represented in the projective continuous-function
Banach space by the smooth Cayley resolvent. -/
def projectiveNevanlinnaJetExpansionBanachMap
    {ι : Type} [Fintype ι]
    (a q : ℂ → ℂ) (n : ι → ℕ) (z : ι → ℂ) :
    C(OnePoint ℝ, (Σ i, Fin (n i)) → ℂ) :=
  projectiveContinuousMapPiCLM fun s =>
    ∑ k : Fin (n s.1),
      projectiveContinuousMapConstCLM (nevanlinnaJetCoeff a q s.2 k (z s.1)) *
        (projectiveResolventBanach (q (z s.1))) ^ (k.1 + 1)

/-- On the upper packet locus, the Banach formula is pointwise the literal forward Nevanlinna
jet-expansion column. -/
theorem projectiveNevanlinnaJetExpansionBanachMap_apply
    {ι : Type} [Fintype ι]
    (a q : ℂ → ℂ) (n : ι → ℕ) (z : ι → ℂ)
    (hz : z ∈ nevanlinnaUpperPacketSet q)
    (t : OnePoint ℝ) :
    projectiveNevanlinnaJetExpansionBanachMap a q n z t =
      projectiveNevanlinnaJetExpansionColumn a q z n t := by
  funext s
  simp only [projectiveNevanlinnaJetExpansionBanachMap,
    projectiveContinuousMapPiCLM_apply, ContinuousMap.sum_apply,
    ContinuousMap.mul_apply, projectiveContinuousMapConstCLM_apply,
    ContinuousMap.pow_apply, projectiveNevanlinnaJetExpansionColumn]
  apply Finset.sum_congr rfl
  intro k hk
  rw [projectiveResolventBanach_apply (q (z s.1)) (hz s.1)]
  cases t <;> simp [projectiveCauchyPower]

/-- The actual finite forward Nevanlinna kernel is a smooth sup-norm family on its upper packet
locus. -/
theorem contDiffOn_projectiveNevanlinnaJetExpansionBanachMap
    {ι : Type} [Fintype ι]
    (a q : ℂ → ℂ) (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (n : ι → ℕ) :
    ContDiffOn ℝ ⊤ (projectiveNevanlinnaJetExpansionBanachMap a q n)
      (nevanlinnaUpperPacketSet q) := by
  have hpi : ContDiffOn ℝ ⊤
      (fun z : ι → ℂ => fun s : Σ i, Fin (n i) =>
        ∑ k : Fin (n s.1),
          projectiveContinuousMapConstCLM
              (nevanlinnaJetCoeff a q s.2 k (z s.1)) *
            (projectiveResolventBanach (q (z s.1))) ^ (k.1 + 1))
      (nevanlinnaUpperPacketSet q) := by
    apply contDiffOn_pi'
    intro s
    apply ContDiffOn.sum
    intro k hk
    have hz : ContDiff ℝ ⊤ (fun z : ι → ℂ => z s.1) :=
      contDiff_apply ℝ ℂ s.1
    have hcoeff0 : ContDiff ℝ ⊤ (nevanlinnaJetCoeff a q s.2 k) :=
      contDiff_real_of_contDiff_complex (contDiff_nevanlinnaJetCoeff ha hq s.2 k)
    have hcoeff : ContDiff ℝ ⊤
        (fun z : ι → ℂ => nevanlinnaJetCoeff a q s.2 k (z s.1)) :=
      hcoeff0.comp hz
    have hconst : ContDiff ℝ ⊤
        (fun z : ι → ℂ =>
          projectiveContinuousMapConstCLM (nevanlinnaJetCoeff a q s.2 k (z s.1))) :=
      (projectiveContinuousMapConstCLM.restrictScalars ℝ).contDiff.comp hcoeff
    have hqreal : ContDiff ℝ ⊤ q := contDiff_real_of_contDiff_complex hq
    have hqz : ContDiff ℝ ⊤ (fun z : ι → ℂ => q (z s.1)) :=
      hqreal.comp hz
    have hpower : ContDiffOn ℝ ⊤
        (fun z : ι → ℂ =>
          (projectiveResolventBanach (q (z s.1))) ^ (k.1 + 1))
        (nevanlinnaUpperPacketSet q) := by
      exact (contDiffOn_projectiveCauchyPowerBanach k.1).comp hqz.contDiffOn
        (fun z hz => hz s.1)
    exact hconst.contDiffOn.mul hpower
  simpa only [projectiveNevanlinnaJetExpansionBanachMap, Function.comp_apply] using!
    (projectiveContinuousMapPiCLM.restrictScalars ℝ).contDiff.comp_contDiffOn hpi

/-- The actual forward Nevanlinna kernel is smooth on an arbitrary open regular locus.  This is
the local form needed for meromorphic Nevanlinna coordinates such as `q = -D/C`. -/
theorem contDiffOn_projectiveNevanlinnaJetExpansionBanachMap_within
    {ι : Type} [Fintype ι]
    (a q : ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (ha : ContDiffOn ℂ ⊤ a U) (hq : ContDiffOn ℂ ⊤ q U)
    (n : ι → ℕ) :
    ContDiffOn ℝ ⊤ (projectiveNevanlinnaJetExpansionBanachMap a q n)
      (nevanlinnaUpperPacketSetWithin q U) := by
  have hpi : ContDiffOn ℝ ⊤
      (fun z : ι → ℂ => fun s : Σ i, Fin (n i) =>
        ∑ k : Fin (n s.1),
          projectiveContinuousMapConstCLM
              (nevanlinnaJetCoeff a q s.2 k (z s.1)) *
            (projectiveResolventBanach (q (z s.1))) ^ (k.1 + 1))
      (nevanlinnaUpperPacketSetWithin q U) := by
    apply contDiffOn_pi'
    intro s
    apply ContDiffOn.sum
    intro k hk
    have hz : ContDiff ℝ ⊤ (fun z : ι → ℂ => z s.1) :=
      contDiff_apply ℝ ℂ s.1
    have hcoeff0 : ContDiffOn ℝ ⊤ (nevanlinnaJetCoeff a q s.2 k) U :=
      contDiffOn_real_of_contDiffOn_complex_of_isOpen hU
        (contDiffOn_nevanlinnaJetCoeff_of_isOpen hU ha hq s.2 k)
    have hcoeff : ContDiffOn ℝ ⊤
        (fun z : ι → ℂ => nevanlinnaJetCoeff a q s.2 k (z s.1))
        (nevanlinnaUpperPacketSetWithin q U) :=
      hcoeff0.comp hz.contDiffOn
        (fun z hzmem => hzmem.2 s.1 (Set.mem_univ s.1))
    have hconst : ContDiffOn ℝ ⊤
        (fun z : ι → ℂ =>
          projectiveContinuousMapConstCLM
            (nevanlinnaJetCoeff a q s.2 k (z s.1)))
        (nevanlinnaUpperPacketSetWithin q U) :=
      (projectiveContinuousMapConstCLM.restrictScalars ℝ).contDiff.comp_contDiffOn hcoeff
    have hqreal : ContDiffOn ℝ ⊤ q U :=
      contDiffOn_real_of_contDiffOn_complex_of_isOpen hU hq
    have hqz : ContDiffOn ℝ ⊤ (fun z : ι → ℂ => q (z s.1))
        (nevanlinnaUpperPacketSetWithin q U) :=
      hqreal.comp hz.contDiffOn
        (fun z hzmem => hzmem.2 s.1 (Set.mem_univ s.1))
    have hpower : ContDiffOn ℝ ⊤
        (fun z : ι → ℂ =>
          (projectiveResolventBanach (q (z s.1))) ^ (k.1 + 1))
        (nevanlinnaUpperPacketSetWithin q U) :=
      (contDiffOn_projectiveCauchyPowerBanach k.1).comp hqz
        (fun z hzmem => hzmem.1 s.1)
    exact hconst.mul hpower
  simpa only [projectiveNevanlinnaJetExpansionBanachMap, Function.comp_apply] using!
    (projectiveContinuousMapPiCLM.restrictScalars ℝ).contDiff.comp_contDiffOn hpi

/-- The genuine bounded-density control obtained from the smooth Banach kernel. -/
def projectiveNevanlinnaJetExpansionSmoothControl
    {ι : Type} [Fintype ι]
    (a q : ℂ → ℂ) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (z : ι → ℂ) :
    Lp ℝ (⊤ : ENNReal) mu →L[ℝ] ((Σ i, Fin (n i)) → ℂ) :=
  linftyLpKernelControl mu
    (ContinuousMap.toLp 1 mu ℝ (projectiveNevanlinnaJetExpansionBanachMap a q n z))

/-- The actual bounded-density Nevanlinna row-evaluation operator is smooth in operator norm. -/
theorem contDiffOn_projectiveNevanlinnaJetExpansionSmoothControl
    {ι : Type} [Fintype ι]
    (a q : ℂ → ℂ) (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (n : ι → ℕ) (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] :
    ContDiffOn ℝ ⊤
      (projectiveNevanlinnaJetExpansionSmoothControl a q n mu)
      (nevanlinnaUpperPacketSet q) := by
  exact (linftyLpKernelControl mu).contDiff.comp_contDiffOn
    ((ContinuousMap.toLp 1 mu ℝ).contDiff.comp_contDiffOn
      (contDiffOn_projectiveNevanlinnaJetExpansionBanachMap a q ha hq n))

/-- Operator-norm smoothness of the genuine bounded-density control on a local meromorphic
regularity locus. -/
theorem contDiffOn_projectiveNevanlinnaJetExpansionSmoothControl_within
    {ι : Type} [Fintype ι]
    (a q : ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (ha : ContDiffOn ℂ ⊤ a U) (hq : ContDiffOn ℂ ⊤ q U)
    (n : ι → ℕ) (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] :
    ContDiffOn ℝ ⊤
      (projectiveNevanlinnaJetExpansionSmoothControl a q n mu)
      (nevanlinnaUpperPacketSetWithin q U) := by
  exact (linftyLpKernelControl mu).contDiff.comp_contDiffOn
    ((ContinuousMap.toLp 1 mu ℝ).contDiff.comp_contDiffOn
      (contDiffOn_projectiveNevanlinnaJetExpansionBanachMap_within
        a q hU ha hq n))

/-- On the upper packet locus, the smooth operator is exactly the existing direct forward
Nevanlinna control, not merely an extension with the same values on finite projective parameters. -/
theorem projectiveNevanlinnaJetExpansionSmoothControl_eq_existing
    {ι : Type} [Fintype ι]
    (a q : ℂ → ℂ) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (η : ℝ) (hη : 0 < η)
    (z : ι → NevanlinnaUpperNodeAtLeast q η) :
    projectiveNevanlinnaJetExpansionSmoothControl a q n mu (fun i => (z i).1) =
      linftyBochnerControl mu
        (projectiveNevanlinnaJetExpansionColumn a q (fun i => (z i).1) n)
        (memLp_projectiveNevanlinnaJetExpansionColumn η hη n mu z) := by
  have hz : (fun i => (z i).1) ∈ nevanlinnaUpperPacketSet q :=
    fun i => hη.trans_le (z i).2
  unfold projectiveNevanlinnaJetExpansionSmoothControl linftyBochnerControl
  rw [linftyLpKernelControl_apply]
  congr 1
  apply Lp.ext
  filter_upwards
    [ContinuousMap.coeFn_toLp (p := (1 : ENNReal)) (𝕜 := ℝ) mu
      (projectiveNevanlinnaJetExpansionBanachMap a q n (fun i => (z i).1)),
     (memLp_projectiveNevanlinnaJetExpansionColumn η hη n mu z).coeFn_toLp]
      with t ht hs
  rw [ht, hs, projectiveNevanlinnaJetExpansionBanachMap_apply
    a q n (fun i => (z i).1) hz t]

end

end GaloisForLFunctions.HTGeometry
