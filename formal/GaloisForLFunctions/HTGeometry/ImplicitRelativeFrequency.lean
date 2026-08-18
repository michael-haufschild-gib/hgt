import GaloisForLFunctions.HTGeometry.HullComparisonMorphism
import GaloisForLFunctions.HTGeometry.CarrierRepresentativeRel
import GaloisForLFunctions.HTGeometry.RelativeHullChartRank
import GaloisForLFunctions.HTGeometry.StripSolutionPhaseRank
import GaloisForLFunctions.HTGeometry.ComplexJetEuclidean
import GaloisForLFunctions.HTGeometry.LinearJet
import GaloisForLFunctions.HTGeometry.MinimalFlowJetVanishing

/-!
# The fibre of the coefficient projection

For a joint carrier of a pair, the projection onto the first component is a comparison morphism, and
its kernel is where every character of the first component is trivial.  On that kernel the first
component of every representative is the base one: the coefficients return.

Two carrier points of the kernel therefore have representatives solving one and the same relation
with varying coefficients, and the jets of the second component alone separate them.
-/

open Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {σ r ρ : ℝ} {n : ℕ}

/-- The joint translation distance dominates the distance of the first component. -/
theorem uniformContinuous_bohrLine_fst {E₁ : Type*} [NormedAddCommGroup E₁]
    (p : ℝ →ᵇ (E₁ × ℂ)) (q : ℝ →ᵇ E₁) (hq : ∀ t : ℝ, q t = (p t).1) :
    UniformContinuous (fun t : BohrLine p => (BohrLine.of q t.val)) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun s t => ?_).uniformContinuous
  rw [BohrLine.dist_eq, BohrLine.dist_eq]
  simp only [NNReal.coe_one, one_mul]
  refine (BoundedContinuousFunction.dist_le dist_nonneg).mpr fun u => ?_
  have hpt : dist (q (u + s.val)) (q (u + t.val))
      ≤ dist (p (u + s.val)) (p (u + t.val)) := by
    rw [hq, hq, Prod.dist_eq]
    exact le_max_left _ _
  refine le_trans hpt ?_
  have := BoundedContinuousFunction.dist_coe_le_dist
    (f := translateBC s.val p) (g := translateBC t.val p) u
  simpa using this

/-- **On the fibre the coefficients return.**  A carrier point at which every character of the first
component is trivial has a representative whose first component is the base one. -/
theorem eqOn_rep_fst_of_mem_bohrHullKernel {E₁ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℂ E₁] [CompleteSpace E₁]
    (hrρ : 0 < r + ρ) {p : ℝ →ᵇ (E₁ × ℂ)} {q : ℝ →ᵇ E₁} (hq : ∀ t : ℝ, q t = (p t).1)
    (hqu : UniformContinuous (fun x => q x)) (hqtb : HasTotallyBoundedOrbit (fun x => q x))
    [MeasurableSpace (BohrHull q)] [BorelSpace (BohrHull q)]
    {rep : BohrHull p → (ℂ → E₁ × ℂ)}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ (r + ρ)))
    (hrepline : ∀ (x : BohrHull p) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval p (x + bohrIota p t))
    {x : BohrHull p}
    (hx : x ∈ bohrHullKernel p (Submodule.span ℚ ((bohrHullFrequencies q : AddSubgroup ℝ) : Set ℝ))) :
    Set.EqOn (fun z => (rep x z).1) (fun z => (rep 0 z).1) (verticalStrip σ (r + ρ)) := by
  have hcmp := uniformContinuous_bohrLine_fst p q hq
  -- the carrier point lies in the kernel of the comparison morphism
  have hker : hullMap p q x = 0 := by
    refine hullMap_eq_zero_of_char_eq_one hqu hqtb hcmp fun μ hμ => ?_
    refine hx μ (isBohrHullFrequency_of_uniformContinuous_compare hcmp hμ) ?_
    exact Submodule.subset_span (by exact hμ)
  -- hence the first component of the representative is the base one along the line
  have hline : ∀ t : ℝ, (rep x ((σ : ℂ) + (t : ℂ) * Complex.I)).1
      = (rep 0 ((σ : ℂ) + (t : ℂ) * Complex.I)).1 := by
    intro t
    have hL : Continuous (Prod.fst : E₁ × ℂ → E₁) := continuous_fst
    have hx1 : (bohrEval p (x + bohrIota p t)).1
        = bohrEval q (hullMap p q (x + bohrIota p t)) :=
      (bohrEval_hullMap hcmp hL (fun s => (hq s).symm ▸ rfl) _).symm
    have h0 : (bohrEval p ((0 : BohrHull p) + bohrIota p t)).1
        = bohrEval q (hullMap p q ((0 : BohrHull p) + bohrIota p t)) :=
      (bohrEval_hullMap hcmp hL (fun s => (hq s).symm ▸ rfl) _).symm
    rw [hrepline x t, hrepline 0 t, hx1, h0, hullMap_add hcmp, hullMap_add hcmp,
      hullMap_bohrIota hcmp, hker, hullMap_zero hcmp]
  -- and therefore on the whole substrip
  have hd1 : DifferentiableOn ℂ (fun z => (rep x z).1) (verticalStrip σ (r + ρ)) :=
    (ContinuousLinearMap.fst ℂ E₁ ℂ).differentiable.comp_differentiableOn (hrepdiff x)
  have hd0 : DifferentiableOn ℂ (fun z => (rep 0 z).1) (verticalStrip σ (r + ρ)) :=
    (ContinuousLinearMap.fst ℂ E₁ ℂ).differentiable.comp_differentiableOn (hrepdiff 0)
  exact eqOn_of_eqOn_line hrρ hd1 hd0 hline

/-- **The relative frequency-rank law for a relation with almost-periodic coefficients.**  On the
fibre of the coefficient projection every representative solves one and the same relation, so the
lower jets of the second component separate the fibre, and the relative rank of the joint frequency
group over the coefficient frequency group is at most `2n`. -/
theorem rank_quotient_le_of_regular_jets_rel {E₁ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℂ E₁] [CompleteSpace E₁]
    (hρ : 0 < ρ) (hrpos : 0 < r)
    {p : ℝ →ᵇ (E₁ × ℂ)} (hpu : UniformContinuous (fun x => p x))
    (hptb : HasTotallyBoundedOrbit (fun x => p x))
    [MeasurableSpace (BohrHull p)] [BorelSpace (BohrHull p)]
    {q : ℝ →ᵇ E₁} (hq : ∀ t : ℝ, q t = (p t).1)
    (hqu : UniformContinuous (fun x => q x)) (hqtb : HasTotallyBoundedOrbit (fun x => q x))
    [MeasurableSpace (BohrHull q)] [BorelSpace (BohrHull q)]
    {Gb : ℝ →ᵇ ((closedStrip σ (r + ρ)) →ᵇ (E₁ × ℂ))}
    {ν : BohrHull p → BohrHull Gb} (hν : Continuous ν)
    {rep : BohrHull p → (ℂ → E₁ × ℂ)}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ (r + ρ)))
    (hrepval : ∀ (x : BohrHull p) (z : closedStrip σ (r + ρ)),
      rep x (z : ℂ) = bohrEval Gb (ν x) z)
    (hrepline : ∀ (x : BohrHull p) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval p (x + bohrIota p t))
    (hn : 0 < n)
    {P : ℝ → (Fin (n + 1) → ℂ) → ℂ}
    {P' : ℝ → (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)}
    {ι : Type*} {τ : ι → ℝ} {S : ι → Set (Fin (n + 1) → ℂ)}
    {L : ι → (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ι → ℝ}
    (hSopen : ∀ i, IsOpen (S i)) (hSconv : ∀ i, Convex ℝ (S i))
    (hPd : ∀ i, ∀ᶠ t : ℝ in nhds (τ i), ∀ y ∈ S i,
      HasFDerivWithinAt (P t) ((P' t y).restrictScalars ℝ) (S i) y)
    (hC : ∀ i, 0 ≤ C i)
    (hbnd : ∀ i, ∀ᶠ t : ℝ in nhds (τ i), ∀ y ∈ S i, ‖P' t y - L i‖ ≤ C i)
    (hdom : ∀ i, C i < ‖partialCoeff (L i) (Fin.last n)‖)
    (hrelrep : ∀ x ∈ bohrHullKernel p
        (Submodule.span ℚ ((bohrHullFrequencies q : AddSubgroup ℝ) : Set ℝ)),
      ∀ s : ℝ, P s (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (fun z => (rep x z).2) ((σ : ℂ) + (s : ℂ) * Complex.I)) = 0)
    (hatlas : ∀ x ∈ bohrHullKernel p
        (Submodule.span ℚ ((bohrHullFrequencies q : AddSubgroup ℝ) : Set ℝ)),
      ∃ i, (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (fun z => (rep x z).2)
          ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I)) ∈ S i) :
    Module.rank ℤ ((bohrHullFrequencies p) ⧸
        ((bohrHullFrequencies q).addSubgroupOf (bohrHullFrequencies p)))
      ≤ ((n * 2 : ℕ) : Cardinal) := by
  classical
  haveI : CompactSpace (BohrHull p) := compactSpace_bohrHull hptb
  have hrρ : r < r + ρ := by linarith
  have hrρ0 : 0 < r + ρ := by linarith
  have hstripsub : verticalStrip σ r ⊆ verticalStrip σ (r + ρ) := by
    intro z hz
    show |z.re - σ| < r + ρ
    have : |z.re - σ| < r := hz
    linarith
  -- the second component of every representative
  have hd2 : ∀ x : BohrHull p,
      DifferentiableOn ℂ (fun z => (rep x z).2) (verticalStrip σ (r + ρ)) := fun x =>
    (ContinuousLinearMap.snd ℂ E₁ ℂ).differentiable.comp_differentiableOn (hrepdiff x)
  have hjetsnd : ∀ (x : BohrHull p) (k : ℕ) (t : ℝ),
      iteratedDeriv k (fun z => (rep x z).2) ((σ : ℂ) + (t : ℂ) * Complex.I)
        = (iteratedDeriv k (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I)).2 := by
    intro x k t
    exact HTGeometry.iteratedDeriv_clm_comp_eqOn (isOpen_verticalStrip σ (r + ρ))
      (ContinuousLinearMap.snd ℂ E₁ ℂ) (hrepdiff x) k (mem_verticalStrip_line hrρ0 σ t)
  -- the jet at each sample time, continuous in the carrier point
  set J : ι → BohrHull p → (Fin (n + 1) → ℂ) := fun i x => fun k : Fin (n + 1) =>
    iteratedDeriv (k : ℕ) (fun z => (rep x z).2) ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I) with hJ
  have hJcont : ∀ i, Continuous (J i) := by
    intro i
    refine continuous_pi fun k => ?_
    have hbase : Continuous fun x : BohrHull p =>
        iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I) :=
      continuous_jet_of_representatives hρ hrpos hrρ hν hrepdiff hrepval (k : ℕ) (τ i)
    have hrw : (fun x : BohrHull p => J i x k)
        = fun x : BohrHull p =>
          (iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I)).2 := by
      funext x
      exact hjetsnd x (k : ℕ) (τ i)
    rw [hrw]
    exact continuous_snd.comp hbase
  set U : ι → Set (BohrHull p) := fun i => {x | J i x ∈ S i} with hU
  have hUopen : ∀ i, IsOpen (U i) := fun i => (hSopen i).preimage (hJcont i)
  have hUcov : ∀ x ∈ bohrHullKernel p
      (Submodule.span ℚ ((bohrHullFrequencies q : AddSubgroup ℝ) : Set ℝ)), ∃ i, x ∈ U i := hatlas
  set Jlow : ι → BohrHull p → (Fin n → ℂ) := fun i x => fun k : Fin n =>
    iteratedDeriv (k : ℕ) (fun z => (rep x z).2) ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I) with hJlow
  have hJlowcont : ∀ i, Continuous (Jlow i) := by
    intro i
    refine continuous_pi fun k => ?_
    have hbase : Continuous fun x : BohrHull p =>
        iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I) :=
      continuous_jet_of_representatives hρ hrpos hrρ hν hrepdiff hrepval (k : ℕ) (τ i)
    have hrw : (fun x : BohrHull p => Jlow i x k)
        = fun x : BohrHull p =>
          (iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I)).2 := by
      funext x
      exact hjetsnd x (k : ℕ) (τ i)
    rw [hrw]
    exact continuous_snd.comp hbase
  -- separation on the fibre
  have hsep : ∀ (i : ι) (x y : BohrHull p), x ∈ U i → y ∈ U i →
      x ∈ bohrHullKernel p (Submodule.span ℚ ((bohrHullFrequencies q : AddSubgroup ℝ) : Set ℝ)) →
      y ∈ bohrHullKernel p (Submodule.span ℚ ((bohrHullFrequencies q : AddSubgroup ℝ) : Set ℝ)) →
      Jlow i x = Jlow i y → x = y := by
    intro i x y hx hy hxK hyK hxy
    have hcoefx := eqOn_rep_fst_of_mem_bohrHullKernel hrρ0 hq hqu hqtb hrepdiff hrepline hxK
    have hcoefy := eqOn_rep_fst_of_mem_bohrHullKernel hrρ0 hq hqu hqtb hrepdiff hrepline hyK
    have hcoef : Set.EqOn (fun z => (rep x z).1) (fun z => (rep y z).1)
        (verticalStrip σ r) := by
      intro z hz
      rw [hcoefx (hstripsub hz), hcoefy (hstripsub hz)]
    have hxev : ∀ᶠ s : ℝ in nhds (τ i), (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (fun z => (rep x z).2)
          ((σ : ℂ) + (s : ℂ) * Complex.I)) ∈ S i :=
      eventually_jet_mem (by linarith) (hd2 x) (hSopen i) hx
    have hyev : ∀ᶠ s : ℝ in nhds (τ i), (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (fun z => (rep y z).2)
          ((σ : ℂ) + (s : ℂ) * Complex.I)) ∈ S i :=
      eventually_jet_mem (by linarith) (hd2 y) (hSopen i) hy
    refine carrier_eq_of_jet_eq_local_rel hrpos hpu hn
      ((hrepdiff x).mono hstripsub) ((hrepdiff y).mono hstripsub) hcoef
      (hSconv i) (hC i) (hdom i) (hPd i) (hbnd i)
      hxev (Filter.Eventually.of_forall (hrelrep x hxK)) hyev
      (Filter.Eventually.of_forall (hrelrep y hyK)) (fun k => ?_)
      (fun t => (hrepline x t)) (fun t => (hrepline y t))
    exact congrFun hxy k
  -- a finite closed cover subordinate to the regular sets
  obtain ⟨M, idx, F, hFclosed, hFsub, hFcov⟩ :=
    exists_finite_closed_cover_subordinate_on
      ((isClosed_bohrHullKernel p
        (Submodule.span ℚ ((bohrHullFrequencies q : AddSubgroup ℝ) : Set ℝ))).isCompact)
      U hUopen hUcov
  refine rank_quotient_bohrHullFrequencies_le_of_charts_rel hpu hptb (bohrHullFrequencies q)
    F hFclosed hFcov
    (fun j x => HTGeometry.complexJetToEuclidean n (Jlow (idx j) x)) (fun j => ?_) (fun j => ?_)
  · exact (HTGeometry.continuous_complexJetToEuclidean n).comp (hJlowcont (idx j)) |>.continuousOn
  · refine HTGeometry.injOn_complexJetToEuclidean_comp ?_
    intro x hx y hy hxy
    exact hsep (idx j) x y (hFsub j hx.1) (hFsub j hy.1) hx.2 hy.2 hxy


end GaloisForLFunctions
