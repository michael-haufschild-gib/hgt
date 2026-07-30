import GaloisForLFunctions.HTGeometry.LocalSelectedLayerSpectralResponse

/-!
# Concrete local-extension matrix chart

One old-system transition channel tensored with an arbitrary matrix on a new
finite local factor contains every selected-layer perturbation used by the
relation-rigidity theorem.  The resulting product-spectrum extension is an
analytic affine matrix chart.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology
open scoped Matrix.Norms.Elementwise

/-- Tensor product of one old transition matrix with a matrix acting on the
new local alphabet. -/
def layerMatrixCoupling
    {α ρ : Type*}
    (transition : Matrix α α ℂ) (edge : Matrix ρ ρ ℂ) :
    Matrix (α × ρ) (α × ρ) ℂ :=
  fun x y => transition x.1 y.1 * edge x.2 y.2

/-- Exchange matrix supported on one unordered pair of local labels. -/
def selectedLayerExchangeMatrix
    {ρ : Type*} [DecidableEq ρ] (r s : ρ) :
    Matrix ρ ρ ℂ :=
  fun u v =>
    if (u = r ∧ v = s) ∨ (u = s ∧ v = r) then 1 else 0

/-- Affine shift line varying only one selected pair while keeping its
difference equal to the line parameter. -/
def selectedPairShiftLine
    {ρ : Type*} [DecidableEq ρ]
    (shift₀ : ρ → ℂ) (r s : ρ) (z : ℂ) : ρ → ℂ :=
  fun u =>
    let z₀ := shift₀ r - shift₀ s
    if u = r then shift₀ r + (z - z₀) / 2
    else if u = s then shift₀ s - (z - z₀) / 2
    else shift₀ u

theorem selectedPairShiftLine_base
    {ρ : Type*} [DecidableEq ρ]
    (shift₀ : ρ → ℂ) (r s : ρ) :
    selectedPairShiftLine shift₀ r s (shift₀ r - shift₀ s) =
      shift₀ := by
  funext u
  by_cases hur : u = r
  · subst u
    simp [selectedPairShiftLine]
  · by_cases hus : u = s
    · subst u
      simp [selectedPairShiftLine, hur]
    · simp [selectedPairShiftLine, hur, hus]

theorem selectedPairShiftLine_pairDifference
    {ρ : Type*} [DecidableEq ρ]
    (shift₀ : ρ → ℂ) {r s : ρ} (hrs : r ≠ s) (z : ℂ) :
    selectedPairShiftLine shift₀ r s z r -
        selectedPairShiftLine shift₀ r s z s = z := by
  simp [selectedPairShiftLine, Ne.symm hrs]
  ring

theorem selectedPairShiftLine_analyticAt
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (shift₀ : ρ → ℂ) (r s : ρ) (z₀ : ℂ) :
    AnalyticAt ℂ (selectedPairShiftLine shift₀ r s) z₀ := by
  have hline :
      AnalyticAt ℂ
        (fun z => (z - (shift₀ r - shift₀ s)) / 2) z₀ :=
    (analyticAt_id.sub analyticAt_const).div_const
  apply AnalyticAt.pi
  intro u
  simp only [selectedPairShiftLine]
  split_ifs
  · exact analyticAt_const.add hline
  · exact analyticAt_const.sub hline
  · exact analyticAt_const

/-- Tensoring with a selected exchange matrix gives exactly the selected
layer coupling used by the response theorem. -/
theorem layerMatrixCoupling_selectedLayerExchangeMatrix
    {α ρ : Type*} [DecidableEq ρ]
    (transition : Matrix α α ℂ) (r s : ρ) :
    layerMatrixCoupling transition
        (selectedLayerExchangeMatrix r s) =
      selectedLayerCoupling transition r s := by
  ext x y
  simp only [layerMatrixCoupling, selectedLayerExchangeMatrix,
    selectedLayerCoupling]
  split_ifs <;> simp_all

theorem layerMatrixCoupling_smul
    {α ρ : Type*}
    (transition : Matrix α α ℂ)
    (g : ℂ) (edge : Matrix ρ ρ ℂ) :
    layerMatrixCoupling transition (g • edge) =
      g • layerMatrixCoupling transition edge := by
  ext x y
  simp [layerMatrixCoupling]
  ring

/-- Product diagonal plus one tensor-local interaction channel. -/
def localExtensionMatrix
    {α ρ : Type*} [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℂ) (shift : ρ → ℂ)
    (transition : Matrix α α ℂ) (edge : Matrix ρ ρ ℂ) :
    Matrix (α × ρ) (α × ρ) ℂ :=
  Matrix.diagonal (layeredEnergy energy shift) +
    layerMatrixCoupling transition edge

@[simp] theorem localExtensionMatrix_zero
    {α ρ : Type*} [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℂ) (shift : ρ → ℂ)
    (transition : Matrix α α ℂ) :
    localExtensionMatrix energy shift transition 0 =
      Matrix.diagonal (layeredEnergy energy shift) := by
  ext x y
  simp [localExtensionMatrix, layerMatrixCoupling]

/-- Restricting the concrete chart to a selected exchange direction gives
the exact affine family required by selected-layer spectral response. -/
theorem localExtensionMatrix_selectedLayer
    {α ρ : Type*} [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℂ) (shift : ρ → ℂ)
    (transition : Matrix α α ℂ)
    (r s : ρ) (g : ℂ) :
    localExtensionMatrix energy shift transition
        (g • selectedLayerExchangeMatrix r s) =
      Matrix.diagonal (layeredEnergy energy shift) +
        g • selectedLayerCoupling transition r s := by
  rw [localExtensionMatrix,
    layerMatrixCoupling_smul,
    layerMatrixCoupling_selectedLayerExchangeMatrix]

/-- The product-spectrum local-extension chart is analytic in all local
shifts and all matrix entries of the new edge channel. -/
theorem localExtensionMatrix_analyticAt
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℂ) (transition : Matrix α α ℂ)
    (p₀ : (ρ → ℂ) × Matrix ρ ρ ℂ) :
    AnalyticAt ℂ
      (fun p =>
        localExtensionMatrix energy p.1 transition p.2) p₀ := by
  apply AnalyticAt.pi
  intro x
  apply AnalyticAt.pi
  intro y
  have hshift :
      AnalyticAt ℂ (fun p : (ρ → ℂ) × Matrix ρ ρ ℂ =>
        p.1 x.2) p₀ := by
    let coord : (ρ → ℂ) →L[ℂ] ℂ :=
      ContinuousLinearMap.proj (R := ℂ) x.2
    exact (coord.analyticAt p₀.1).comp analyticAt_fst
  have hlocal :
      AnalyticAt ℂ (fun p : (ρ → ℂ) × Matrix ρ ρ ℂ =>
        p.2 x.2 y.2) p₀ := by
    let row : Matrix ρ ρ ℂ →L[ℂ] (ρ → ℂ) :=
      ContinuousLinearMap.proj (R := ℂ) x.2
    let col : (ρ → ℂ) →L[ℂ] ℂ :=
      ContinuousLinearMap.proj (R := ℂ) y.2
    let entry : Matrix ρ ρ ℂ →L[ℂ] ℂ := col.comp row
    exact (entry.analyticAt p₀.2).comp analyticAt_snd
  by_cases hxy : x = y
  · subst y
    simpa [localExtensionMatrix, layeredEnergy,
      layerMatrixCoupling] using!
        (analyticAt_const.add hshift).add
          (analyticAt_const.mul hlocal)
  · simpa [localExtensionMatrix, layeredEnergy,
      layerMatrixCoupling, hxy] using!
        analyticAt_const.mul hlocal

/-- Every simple product energy has a locally analytic characteristic-root
branch in the concrete local-extension chart. -/
theorem exists_localExtensionEigenvalueBranch
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℂ) (shift₀ : ρ → ℂ)
    (transition : Matrix α α ℂ)
    (hsimple : Function.Injective (layeredEnergy energy shift₀))
    (i : α × ρ) :
    ∃ branch :
        ((ρ → ℂ) × Matrix ρ ρ ℂ) → ℂ,
      AnalyticAt ℂ branch (shift₀, 0) ∧
      branch (shift₀, 0) =
        layeredEnergy energy shift₀ i ∧
      (∀ᶠ p in 𝓝 (shift₀, 0),
        matrixCharpolyRelation
          (localExtensionMatrix energy p.1 transition p.2,
            branch p) = 0) := by
  apply analyticMatrixFamily_eigenvalueBranch
    (localExtensionMatrix_analyticAt energy transition (shift₀, 0))
    (layeredEnergy energy shift₀) hsimple
  · exact localExtensionMatrix_zero energy shift₀ transition

/-- One common connected neighbourhood carrying every labeled simple
eigenvalue branch of a product-spectrum local extension. -/
structure LocalExtensionEigenbranchChart
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℂ) (shift₀ : ρ → ℂ)
    (transition : Matrix α α ℂ) where
  branch : α × ρ →
    ((ρ → ℂ) × Matrix ρ ρ ℂ) → ℂ
  U : Set ((ρ → ℂ) × Matrix ρ ρ ℂ)
  isOpen_U : IsOpen U
  isPreconnected_U : IsPreconnected U
  center_mem : (shift₀, 0) ∈ U
  analyticOn_branch :
    ∀ i, AnalyticOnNhd ℂ (branch i) U
  base :
    ∀ i, branch i (shift₀, 0) =
      layeredEnergy energy shift₀ i
  simple :
    ∀ p ∈ U, Function.Injective (fun i => branch i p)
  root :
    ∀ p ∈ U, ∀ i,
      matrixCharpolyRelation
        (localExtensionMatrix energy p.1 transition p.2,
          branch i p) = 0

/-- A simple product spectrum supplies a common analytic chart for all
labeled branches. -/
theorem exists_localExtensionEigenbranchChart
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℂ) (shift₀ : ρ → ℂ)
    (transition : Matrix α α ℂ)
    (hsimple : Function.Injective (layeredEnergy energy shift₀)) :
    Nonempty
      (LocalExtensionEigenbranchChart
        energy shift₀ transition) := by
  classical
  choose branch hbranch hbase hroot using
    fun i =>
      exists_localExtensionEigenvalueBranch
        energy shift₀ transition hsimple i
  have hbranchAll :
      ∀ᶠ p in 𝓝 (shift₀, 0),
        ∀ i, AnalyticAt ℂ (branch i) p := by
    rw [Filter.eventually_all]
    intro i
    exact (hbranch i).eventually_analyticAt
  have hrootAll :
      ∀ᶠ p in 𝓝 (shift₀, 0),
        ∀ i,
          matrixCharpolyRelation
            (localExtensionMatrix energy p.1 transition p.2,
              branch i p) = 0 := by
    rw [Filter.eventually_all]
    exact hroot
  have hsimpleAll :
      ∀ᶠ p in 𝓝 (shift₀, 0),
        Function.Injective (fun i => branch i p) := by
    have hpairs :
        ∀ i j : α × ρ, i ≠ j →
          ∀ᶠ p in 𝓝 (shift₀, 0),
            branch i p ≠ branch j p := by
      intro i j hij
      have hdiff :
          ContinuousAt
            (fun p => branch i p - branch j p)
            (shift₀, 0) :=
        ((hbranch i).sub (hbranch j)).continuousAt
      have hdiffNe :
          branch i (shift₀, 0) -
              branch j (shift₀, 0) ≠ 0 := by
        rw [sub_ne_zero, hbase i, hbase j]
        exact fun heq => hij (hsimple heq)
      have hev := hdiff (isOpen_ne.mem_nhds hdiffNe)
      filter_upwards [hev] with p hp
      exact sub_ne_zero.mp hp
    have hall :
        ∀ᶠ p in 𝓝 (shift₀, 0),
          ∀ i j : α × ρ, i ≠ j →
            branch i p ≠ branch j p := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      by_cases hij : i = j
      · filter_upwards [] with p
        exact fun h => (h hij).elim
      · filter_upwards [hpairs i j hij] with p hp
        exact fun _ => hp
    filter_upwards [hall] with p hp
    rw [Function.injective_iff_pairwise_ne]
    exact hp
  have hboth :
      {p |
        (∀ i, AnalyticAt ℂ (branch i) p) ∧
        Function.Injective (fun i => branch i p) ∧
        (∀ i,
          matrixCharpolyRelation
            (localExtensionMatrix energy p.1 transition p.2,
              branch i p) = 0)} ∈ 𝓝 (shift₀, 0) := by
    filter_upwards [hbranchAll, hsimpleAll, hrootAll]
      with p hpa hps hpr
    exact ⟨hpa, hps, hpr⟩
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp hboth
  let U :=
    Metric.ball
      ((shift₀, 0) :
        (ρ → ℂ) × Matrix ρ ρ ℂ) ε
  refine ⟨{
    branch := branch
    U := U
    isOpen_U := Metric.isOpen_ball
    isPreconnected_U := Metric.isPreconnected_ball
    center_mem := by simpa [U] using hε
    analyticOn_branch := ?_
    base := hbase
    simple := ?_
    root := ?_
  }⟩
  · intro i p hp
    exact (hball hp).1 i
  · intro p hp
    exact (hball hp).2.1
  · intro p hp i
    exact (hball hp).2.2 i

end

end GaloisForLFunctions.HTGeometry
