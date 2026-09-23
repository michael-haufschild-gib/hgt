import GaloisForLFunctions.HTGeometry.LocalSpectralPacketLocality

/-!
# Local spectral-jet causality for actual finite generators

This file packages one analytic simple-eigenvalue branch for every product configuration and proves
that every positive-order jet restricted to an interaction packet is local on exactly the sites
touched by that packet. A higher Möbius observer therefore annihilates the jet whenever one of its
changed sites lies outside the packet support. Local alphabets may vary from site to site.
-/

open Filter Topology
open scoped Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

/-- Coordinate locality for dependent product alphabets. -/
def DependentCoordinateLocalOn
    {V : Type*} {A : V → Type*} {R : Type*}
    (S : Set V) (f : (∀ v, A v) → R) : Prop :=
  ∀ x y, (∀ v, v ∈ S → x v = y v) → f x = f y

def dependentUpdateOnFinset
    {V : Type*} [DecidableEq V] {A : V → Type*}
    (x alternative : ∀ v, A v) (s : Finset V) : ∀ v, A v :=
  fun v => if v ∈ s then alternative v else x v

/-- Higher Boolean mixed difference for a dependent product alphabet. -/
def dependentHigherCoordinateContrast
    {V : Type*} [DecidableEq V] {A : V → Type*}
    {R : Type*} [CommRing R]
    (x alternative : ∀ v, A v) (sites : Finset V)
    (f : (∀ v, A v) → R) : R :=
  finsetMobiusResponse sites
    (fun active => f (dependentUpdateOnFinset x alternative active))

/-- A dependent higher contrast vanishes whenever its local function misses one changed site. -/
theorem dependentHigherCoordinateContrast_eq_zero_of_local_miss
    {V : Type*} [DecidableEq V] {A : V → Type*}
    {R : Type*} [CommRing R]
    {support : Set V} {f : (∀ v, A v) → R}
    (hf : DependentCoordinateLocalOn support f)
    (x alternative : ∀ v, A v) {sites : Finset V} {i : V}
    (hi_sites : i ∈ sites) (hi : i ∉ support) :
    dependentHigherCoordinateContrast x alternative sites f = 0 := by
  have hinvariant :
      ∀ active,
        f (dependentUpdateOnFinset x alternative (insert i active)) =
          f (dependentUpdateOnFinset x alternative active) := by
    intro active
    apply hf
    intro v hv
    have hvi : v ≠ i := by
      intro h
      exact hi (h ▸ hv)
    simp [dependentUpdateOnFinset, hvi]
  unfold dependentHigherCoordinateContrast
  exact finsetMobiusResponse_eq_zero_of_insert_invariant
    hi_sites _ hinvariant

namespace FiniteLocalInteractionFamily

variable
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]

/-- A fixed choice of the unique simple-eigenvalue germ born from each product configuration. -/
noncomputable def productEigenvalueBranch
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x : ∀ v, A v) : (E → ℂ) → ℂ :=
  Classical.choose
    (affineMatrixFamily_eigenvalueBranch
      (onsiteProductEnergy onsite) hinj L.globalInteraction x)

omit [∀ v, Nonempty (A v)] in
theorem productEigenvalueBranch_spec
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (x : ∀ v, A v) :
    AnalyticAt ℂ (L.productEigenvalueBranch onsite hinj x) 0 ∧
      L.productEigenvalueBranch onsite hinj x 0 =
        onsiteProductEnergy onsite x ∧
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            L.globalInteraction coupling,
            L.productEigenvalueBranch onsite hinj x coupling) = 0 :=
  Classical.choose_spec
    (affineMatrixFamily_eigenvalueBranch
      (onsiteProductEnergy onsite) hinj L.globalInteraction x)

/-- **Positive local spectral jets are actually local.** The evaluated `n`th eigenvalue jet of an
active interaction packet depends only on the product configuration over the union of that
packet's site supports. -/
theorem packetEigenvalueJet_coordinateLocal
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (packet : Finset E) {n : ℕ} (hn : n ≠ 0)
    (directions :
      Fin n → ({e : E // e ∈ packet} → ℂ)) :
    DependentCoordinateLocalOn
      (L.packetSiteSupport packet : Set V)
      (fun x =>
        iteratedFDeriv ℂ n
          (fun coupling =>
            L.productEigenvalueBranch onsite hinj x
              (extendCouplingFromPacket packet coupling))
          0 directions) := by
  intro x y hxy
  have hx := L.productEigenvalueBranch_spec onsite hinj x
  have hy := L.productEigenvalueBranch_spec onsite hinj y
  have hderiv :=
    L.restrictedBranches_iteratedFDeriv_eq_of_positive
      onsite hinj
      (L.productEigenvalueBranch onsite hinj x)
      (L.productEigenvalueBranch onsite hinj y)
      hx.1 hy.1 hx.2.1 hy.2.1 hx.2.2 hy.2.2
      packet (fun v hv => hxy v hv) hn
  exact congrArg (fun p => p directions) hderiv

/-- **Actual local-generator observer causality.** A higher site observer containing a site outside
the active packet support annihilates every positive-order evaluated eigenvalue jet exactly. -/
theorem higherCoordinateContrast_packetEigenvalueJet_eq_zero_of_miss
    (L : FiniteLocalInteractionFamily V E A)
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (packet : Finset E) {n : ℕ} (hn : n ≠ 0)
    (directions :
      Fin n → ({e : E // e ∈ packet} → ℂ))
    (x alternative : ∀ v, A v) {sites : Finset V} {i : V}
    (hi_sites : i ∈ sites)
    (hi : i ∉ L.packetSiteSupport packet) :
    dependentHigherCoordinateContrast x alternative sites
      (fun config =>
        iteratedFDeriv ℂ n
          (fun coupling =>
            L.productEigenvalueBranch onsite hinj config
              (extendCouplingFromPacket packet coupling))
          0 directions) = 0 := by
  apply dependentHigherCoordinateContrast_eq_zero_of_local_miss
    (L.packetEigenvalueJet_coordinateLocal onsite hinj packet hn directions)
    x alternative hi_sites
  simpa using hi

end FiniteLocalInteractionFamily
end GaloisForLFunctions.HTGeometry
