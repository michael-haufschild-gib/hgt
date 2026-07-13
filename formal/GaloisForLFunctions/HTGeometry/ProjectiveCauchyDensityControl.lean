import GaloisForLFunctions.HTGeometry.LinftyDensityControl
import GaloisForLFunctions.HTGeometry.LinftyPositiveAperture
import GaloisForLFunctions.HTGeometry.NevanlinnaJetTriangular
import GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryAlgebra
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Projective Cauchy and Nevanlinna control by bounded densities

Parameter Cauchy powers extend continuously to the one-point compactification of the real line by
the value zero at infinity.  For an infinite-support projective probability law, the resulting
finite Cauchy-jet packet is exactly controllable by real `L∞` density perturbations.  Disjoint
frozen and target packets retain constrained surjectivity.  The triangular Nevanlinna jet
equivalence then upgrades this statement to genuine analytic Nevanlinna jets.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology
open MeasureTheory
open scoped OnePoint

noncomputable section

/-- A parameter Cauchy power extended by zero at the projective infinity point. -/
def projectiveCauchyPower (x : ℂ) (k : ℕ) : OnePoint ℝ → ℂ :=
  fun t => t.elim 0 (fun r : ℝ => (((r : ℂ) - x)⁻¹) ^ (k + 1))

/-- The projective Cauchy power vanishes at infinity. -/
@[simp] theorem projectiveCauchyPower_infty (x : ℂ) (k : ℕ) :
    projectiveCauchyPower x k ∞ = 0 := by
  simp [projectiveCauchyPower]

/-- On the finite chart it is the ordinary Cauchy power. -/
@[simp] theorem projectiveCauchyPower_coe (x : ℂ) (k : ℕ) (t : ℝ) :
    projectiveCauchyPower x k (t : OnePoint ℝ) = (((t : ℂ) - x)⁻¹) ^ (k + 1) := by
  simp [projectiveCauchyPower]

/-- A Cauchy power with nonreal pole is continuous on the projective real line. -/
theorem continuous_projectiveCauchyPower (x : ℂ) (hx : x.im ≠ 0) (k : ℕ) :
    Continuous (projectiveCauchyPower x k) := by
  rw [OnePoint.continuous_iff]
  constructor
  · simp only [projectiveCauchyPower_coe, projectiveCauchyPower_infty]
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    have hnorm : Tendsto (fun t : ℝ => ‖(t : ℂ) - x‖) (Bornology.cobounded ℝ) atTop := by
      have hlower : Tendsto (fun t : ℝ => ‖t‖ + (-‖x‖))
          (Bornology.cobounded ℝ) atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_norm_cobounded_atTop
      apply tendsto_atTop_mono' _ _ hlower
      filter_upwards [] with t
      simpa using norm_sub_norm_le (t : ℂ) x
    have hden : Tendsto (fun t : ℝ => (t : ℂ) - x)
        (Bornology.cobounded ℝ) (Bornology.cobounded ℂ) :=
      tendsto_norm_atTop_iff_cobounded.mp hnorm
    simpa only [Function.comp_apply, zero_pow (Nat.succ_ne_zero k)] using
      (tendsto_inv₀_cobounded.comp hden).pow (k + 1)
  · change Continuous (fun t : ℝ => (((t : ℂ) - x)⁻¹) ^ (k + 1))
    apply Continuous.pow
    apply Continuous.inv₀
    · fun_prop
    · intro t ht
      have him : -x.im = 0 := by
        simpa using congrArg Complex.im ht
      exact hx (neg_eq_zero.mp him)

/-- The complete finite Cauchy-jet column at one projective parameter. -/
def projectiveCauchyJetColumn
    {ι : Type*} (x : ι → ℂ) (n : ι → ℕ) (t : OnePoint ℝ) :
    ((Σ i, Fin (n i)) → ℂ) :=
  fun s => projectiveCauchyPower (x s.1) s.2 t

/-- A finite projective parameter gives the ordinary Cauchy-jet column. -/
@[simp] theorem projectiveCauchyJetColumn_coe
    {ι : Type*} (x : ι → ℂ) (n : ι → ℕ) (t : ℝ) :
    projectiveCauchyJetColumn x n (t : OnePoint ℝ) =
      cauchyJetColumn x n (fun _ : Unit => (t : ℂ)) () := by
  funext s
  simp [projectiveCauchyJetColumn, cauchyJetColumn]

/-- The projective Cauchy-jet column varies continuously in its parameter. -/
theorem continuous_projectiveCauchyJetColumn
    {ι : Type*} (x : ι → ℂ) (hx : ∀ i, (x i).im ≠ 0) (n : ι → ℕ) :
    Continuous (projectiveCauchyJetColumn x n) := by
  apply continuous_pi
  intro s
  exact continuous_projectiveCauchyPower (x s.1) (hx s.1) s.2

/-- The continuous projective packet is `L¹` for every finite projective measure. -/
theorem memLp_projectiveCauchyJetColumn
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hx : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] :
    MeasureTheory.MemLp (projectiveCauchyJetColumn x n) 1 mu := by
  exact (continuous_projectiveCauchyJetColumn x hx n).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Bounded densities exactly control the packet when the measure support contains an injective
infinite real parameter family. -/
theorem projectiveCauchyJet_linftyBochnerControl_surjective
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Infinite κ]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (t : κ → ℝ) (ht : Function.Injective t)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (htsupport : ∀ k, (t k : OnePoint ℝ) ∈ mu.support) :
    Function.Surjective
      (linftyBochnerControl mu (projectiveCauchyJetColumn x n)
        (memLp_projectiveCauchyJetColumn x (fun i => (hupper i).ne') n mu)) := by
  let K := projectiveCauchyJetColumn x n
  let hK := memLp_projectiveCauchyJetColumn x (fun i => (hupper i).ne') n mu
  apply linftyBochnerControl_surjective_of_support_finsupp
    mu K hK (continuous_projectiveCauchyJetColumn x (fun i => (hupper i).ne') n)
    (fun k => (t k : OnePoint ℝ)) htsupport
  have hsurj := cauchyJetRealLinearCombination_surjective x hx hupper n t ht
  simpa [K, projectiveCauchyJetColumn, projectiveCauchyPower,
    cauchyJetRealLinearCombination, cauchyJetColumn] using hsurj

/-- Finite real parameters belonging to the topological support of a projective measure. -/
def finiteProjectiveSupport (mu : Measure (OnePoint ℝ)) : Type :=
  {t : ℝ // (t : OnePoint ℝ) ∈ mu.support}

/-- Infinite projective support remains infinite after the single infinity point is removed. -/
theorem infinite_finiteProjectiveSupport
    (mu : Measure (OnePoint ℝ)) (hmu : mu.support.Infinite) :
    Infinite (finiteProjectiveSupport mu) := by
  rw [← not_finite_iff_infinite]
  intro hfinite
  letI : Finite (finiteProjectiveSupport mu) := hfinite
  have hrange :
      (Set.range (fun t : finiteProjectiveSupport mu => (t.1 : OnePoint ℝ))).Finite :=
    Set.finite_range _
  have hsfin : mu.support.Finite := (hrange.insert ∞).subset (by
    intro y hy
    induction y using OnePoint.rec with
    | infty => exact Set.mem_insert _ _
    | coe t =>
        apply Set.mem_insert_iff.mpr
        right
        exact ⟨⟨t, hy⟩, rfl⟩)
  exact hmu hsfin

/-- Every infinite-support projective finite measure has surjective bounded-density control of
each finite upper-half-plane Cauchy-jet packet. -/
theorem projectiveCauchyJet_linftyBochnerControl_surjective_of_infiniteSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (hmu : mu.support.Infinite) :
    Function.Surjective
      (linftyBochnerControl mu (projectiveCauchyJetColumn x n)
        (memLp_projectiveCauchyJetColumn x (fun i => (hupper i).ne') n mu)) := by
  letI : Infinite (finiteProjectiveSupport mu) := infinite_finiteProjectiveSupport mu hmu
  exact projectiveCauchyJet_linftyBochnerControl_surjective
    x hx hupper n (fun t : finiteProjectiveSupport mu => t.1)
    (fun _ _ h => Subtype.ext h) mu (fun t => t.2)

/-- Coordinate evaluation commutes with the finite-dimensional Bochner control integral. -/
theorem linftyBochnerControl_apply_pi
    {α σ : Type*} [MeasurableSpace α] [Fintype σ]
    (mu : Measure α) [IsFiniteMeasure mu]
    (K : α → (σ → ℂ)) (hK : MemLp K 1 mu)
    (w : Lp ℝ (⊤ : ENNReal) mu) (s : σ) :
    linftyBochnerControl mu K hK w s = ∫ x, (w x) • K x s ∂mu := by
  rw [linftyBochnerControl_apply]
  have hint : Integrable (fun x => (w x) • K x) mu := by
    exact (ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] (σ → ℂ) →L[ℝ] (σ → ℂ)).integrable_of_bilin_of_bdd_left
        ‖w‖ (Lp.memLp w).1 (linfty_ae_abs_le_norm mu w)
        (hK.integrable (by norm_num))
  let ev : (σ → ℂ) →L[ℝ] ℂ :=
    LinearMap.mkContinuous
      { toFun := fun v => v s
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      1 (fun v => by simpa using norm_le_pi_norm v s)
  exact (ev.integral_comp_comm hint).symm

/-- A disjoint target projective Cauchy-jet packet remains exactly controllable by bounded
densities after a frozen packet is annihilated. -/
theorem constrainedProjectiveCauchyJet_linftyBochnerControl_surjective
    {ιf ιt : Type*} [Fintype ιf] [DecidableEq ιf]
    [Fintype ιt] [DecidableEq ιt]
    (xf : ιf → ℂ) (hxf : Function.Injective xf)
    (xt : ιt → ℂ) (hxt : Function.Injective xt)
    (hcross : ∀ i j, xf i ≠ xt j)
    (hupperf : ∀ i, 0 < (xf i).im) (huppert : ∀ i, 0 < (xt i).im)
    (nf : ιf → ℕ) (nt : ιt → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] (hmu : mu.support.Infinite) :
    Function.Surjective
      ((linftyBochnerControl mu (projectiveCauchyJetColumn xt nt)
          (memLp_projectiveCauchyJetColumn xt (fun i => (huppert i).ne') nt mu)).toLinearMap.domRestrict
        (LinearMap.ker
          (linftyBochnerControl mu (projectiveCauchyJetColumn xf nf)
            (memLp_projectiveCauchyJetColumn xf (fun i => (hupperf i).ne') nf mu)).toLinearMap)) := by
  let x : ιf ⊕ ιt → ℂ := Sum.elim xf xt
  let n : ιf ⊕ ιt → ℕ := Sum.elim nf nt
  have hx : Function.Injective x := by
    intro a b hab
    rcases a with i | i <;> rcases b with j | j
    · exact congrArg Sum.inl (hxf hab)
    · exact False.elim (hcross i j hab)
    · exact False.elim (hcross j i hab.symm)
    · exact congrArg Sum.inr (hxt hab)
  have hupper : ∀ i, 0 < (x i).im := by
    intro i
    rcases i with i | i
    · exact hupperf i
    · exact huppert i
  have hsurj := projectiveCauchyJet_linftyBochnerControl_surjective_of_infiniteSupport
    x hx hupper n mu hmu
  intro y
  let z : ((Σ i, Fin (n i)) → ℂ) := fun q =>
    match q with
    | ⟨Sum.inl _, _⟩ => 0
    | ⟨Sum.inr i, j⟩ => y ⟨i, j⟩
  obtain ⟨w, hw⟩ := hsurj z
  have hwf :
      linftyBochnerControl mu (projectiveCauchyJetColumn xf nf)
        (memLp_projectiveCauchyJetColumn xf (fun i => (hupperf i).ne') nf mu) w = 0 := by
    funext q
    have hq := congrFun hw ⟨Sum.inl q.1, q.2⟩
    rw [linftyBochnerControl_apply_pi] at hq
    rw [linftyBochnerControl_apply_pi]
    simpa [x, n, z, projectiveCauchyJetColumn] using hq
  refine ⟨⟨w, hwf⟩, ?_⟩
  funext q
  have hq := congrFun hw ⟨Sum.inr q.1, q.2⟩
  change linftyBochnerControl mu (projectiveCauchyJetColumn xt nt)
    (memLp_projectiveCauchyJetColumn xt (fun i => (huppert i).ne') nt mu) w q = y q
  rw [linftyBochnerControl_apply_pi]
  rw [linftyBochnerControl_apply_pi] at hq
  simpa [x, n, z, projectiveCauchyJetColumn] using hq

/-- Bounded-density Nevanlinna-jet control obtained from projective Cauchy control by the exact
triangular jet equivalence. -/
def projectiveNevanlinnaJetLinftyControl
    {ι : Type*} [Fintype ι]
    (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu]
    (hupper : ∀ i, 0 < (q (z i)).im) :
    Lp ℝ (⊤ : ENNReal) mu →ₗ[ℝ] ((Σ i, Fin (n i)) → ℂ) :=
  ((nevanlinnaJetPacketLinearEquiv a q z n ha hq).restrictScalars ℝ).toLinearMap.comp
    (linftyBochnerControl mu (projectiveCauchyJetColumn (fun i => q (z i)) n)
      (memLp_projectiveCauchyJetColumn (fun i => q (z i))
        (fun i => (hupper i).ne') n mu)).toLinearMap

/-- The genuine Nevanlinna-jet column on the projective parameter line. -/
def projectiveNevanlinnaJetColumn
    {ι : Type*}
    (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0)
    (t : OnePoint ℝ) : ((Σ i, Fin (n i)) → ℂ) :=
  nevanlinnaJetPacketLinearEquiv a q z n ha hq
    (projectiveCauchyJetColumn (fun i => q (z i)) n t)

/-- The genuine perturbation column vanishes at the infinity parameter. -/
@[simp] theorem projectiveNevanlinnaJetColumn_infty
    {ι : Type*}
    (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0) :
    projectiveNevanlinnaJetColumn a q z n ha hq ∞ = 0 := by
  have hzero : projectiveCauchyJetColumn (fun i => q (z i)) n ∞ = 0 := by
    funext s
    simp [projectiveCauchyJetColumn]
  rw [projectiveNevanlinnaJetColumn, hzero, map_zero]

/-- On every finite parameter, the projective column is exactly the genuine iterated analytic jet. -/
theorem projectiveNevanlinnaJetColumn_coe_eq_actualJet
    {ι : Type*} {a q : ℂ → ℂ}
    (haCont : ContDiff ℂ ⊤ a) (hqCont : ContDiff ℂ ⊤ q)
    (z : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0)
    (t : ℝ) (hden : ∀ i, (t : ℂ) - q (z i) ≠ 0) :
    projectiveNevanlinnaJetColumn a q z n ha hq (t : OnePoint ℝ) =
      fun s : Σ i, Fin (n i) =>
        iteratedDeriv s.2 (fun w => a w * ((t : ℂ) - q w)⁻¹) (z s.1) := by
  exact (nevanlinnaJetPacket_eq_packetLinearEquiv
    haCont hqCont z n (t : ℂ) hden ha hq).symm

/-- **Constrained genuine Nevanlinna-jet controllability in the literal `L∞` chart.** For an
infinite-support projective law, every disjoint finite target packet remains onto on the exact
bounded-density tangent kernel of the frozen packet. -/
theorem constrainedProjectiveNevanlinnaJet_linftyControl_surjective
    {ιf ιt : Type*} [Fintype ιf] [DecidableEq ιf]
    [Fintype ιt] [DecidableEq ιt]
    (a q : ℂ → ℂ)
    (zf : ιf → ℂ) (zt : ιt → ℂ)
    (hqf_inj : Function.Injective (fun i => q (zf i)))
    (hqt_inj : Function.Injective (fun i => q (zt i)))
    (hcross : ∀ i j, q (zf i) ≠ q (zt j))
    (hupperf : ∀ i, 0 < (q (zf i)).im) (huppert : ∀ i, 0 < (q (zt i)).im)
    (nf : ιf → ℕ) (nt : ιt → ℕ)
    (haf : ∀ i, a (zf i) ≠ 0) (hat : ∀ i, a (zt i) ≠ 0)
    (hqdf : ∀ i, deriv q (zf i) ≠ 0) (hqdt : ∀ i, deriv q (zt i) ≠ 0)
    (mu : Measure (OnePoint ℝ)) [IsFiniteMeasure mu] (hmu : mu.support.Infinite) :
    Function.Surjective
      ((projectiveNevanlinnaJetLinftyControl a q zt nt hat hqdt mu huppert).domRestrict
        (LinearMap.ker
          (projectiveNevanlinnaJetLinftyControl a q zf nf haf hqdf mu hupperf))) := by
  exact constrainedControl_surjective_of_linearEquiv
    (linftyBochnerControl mu (projectiveCauchyJetColumn (fun i => q (zf i)) nf)
      (memLp_projectiveCauchyJetColumn (fun i => q (zf i))
        (fun i => (hupperf i).ne') nf mu)).toLinearMap
    (linftyBochnerControl mu (projectiveCauchyJetColumn (fun i => q (zt i)) nt)
      (memLp_projectiveCauchyJetColumn (fun i => q (zt i))
        (fun i => (huppert i).ne') nt mu)).toLinearMap
    ((nevanlinnaJetPacketLinearEquiv a q zf nf haf hqdf).restrictScalars ℝ)
    ((nevanlinnaJetPacketLinearEquiv a q zt nt hat hqdt).restrictScalars ℝ)
    (constrainedProjectiveCauchyJet_linftyBochnerControl_surjective
      (fun i => q (zf i)) hqf_inj (fun i => q (zt i)) hqt_inj hcross
      hupperf huppert nf nt mu hmu)

end
end GaloisForLFunctions.HTGeometry
