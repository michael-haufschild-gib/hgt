import GaloisForLFunctions.HTGeometry.HomogeneousEuclideanNoGo
import GaloisForLFunctions.HTGeometry.HullChartFrequencyRank
import GaloisForLFunctions.HTGeometry.BohrHullBorel

/-!
# Strict frequency-rank bound from a global chart

A single globally injective continuous chart of the phase carrier into `ℝ^k` bounds the rational
rank of the frequency group by `k - 1`, not merely by `k`: an independent packet of `k` frequencies
would give a continuous injection of an open cube into the carrier, so the carrier's image would
have interior, and homogeneity of the carrier plus invariance of domain would make that image
clopen in `ℝ^k`, contradicting compactness.

This is the strict form behind Cartwright's frequency theorem.
-/

open Metric Set Topology

namespace GaloisForLFunctions

open scoped BoundedContinuousFunction

variable {V : Type*} [NormedAddCommGroup V] {f : ℝ →ᵇ V}

/-- The open unit cube. -/
def openUnitCube (r : ℕ) : Set (EuclideanSpace ℝ (Fin r)) := {x | ∀ j, x j ∈ Ioo (0 : ℝ) 1}

theorem isOpen_openUnitCube (r : ℕ) : IsOpen (openUnitCube r) := by
  have : openUnitCube r = ⋂ j : Fin r, (fun x : EuclideanSpace ℝ (Fin r) => x j) ⁻¹' Ioo 0 1 := by
    ext x
    simp [openUnitCube]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    (isOpen_Ioo).preimage ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous)

theorem openUnitCube_nonempty (r : ℕ) : (openUnitCube r).Nonempty := by
  refine ⟨(WithLp.toLp 2) (fun _ => (1 / 2 : ℝ)), fun j => ?_⟩
  constructor <;> norm_num

theorem openUnitCube_subset (r : ℕ) : openUnitCube r ⊆ unitCube r := by
  intro x hx j
  exact ⟨le_of_lt (hx j).1, le_of_lt (hx j).2⟩

/-- The Bohr hull is homogeneous: translation carries any point to any other. -/
theorem homogeneous_bohrHull (f : ℝ →ᵇ V) (x y : BohrHull f) :
    ∃ h : BohrHull f ≃ₜ BohrHull f, h x = y :=
  ⟨Homeomorph.addLeft (y - x), by simp⟩

/-- **A globally injective chart bounds an independent packet strictly.** -/
theorem card_lt_of_hull_global_chart (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {r : ℕ} {lam : Fin r → ℝ} (hind : LinearIndependent ℚ lam)
    (hlam : ∀ j, IsBohrHullFrequency f (lam j))
    {k : ℕ} (hk : 0 < k) (J : BohrHull f → EuclideanSpace ℝ (Fin k))
    (hJc : Continuous J) (hJi : Function.Injective J) : r < k := by
  classical
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  have hle : r ≤ k :=
    card_le_of_hull_charts hf htb hind hlam (N := 1) (fun _ => Set.univ)
      (fun _ => isClosed_univ) (fun _ => ⟨0, Set.mem_univ _⟩) (fun _ => J)
      (fun _ => hJc.continuousOn) (fun _ => hJi.injOn)
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · omega
  refine lt_of_le_of_ne hle fun hrk => ?_
  subst hrk
  haveI : Nontrivial (EuclideanSpace ℝ (Fin r)) := by
    refine ⟨0, (WithLp.toLp 2) (fun _ => (1 : ℝ)), ?_⟩
    intro hcon
    have := congrFun (congrArg (WithLp.ofLp) hcon) ⟨0, hrpos⟩
    simp at this
  obtain ⟨φ, hφcont, hφval⟩ := exists_continuous_hullParameter hf htb hind hlam
  set Ψ : EuclideanSpace ℝ (Fin r) → BohrHull f := fun v => φ fun j => Real.pi * v j with hΨ
  have hΨcont : Continuous Ψ := by
    refine hφcont.comp (continuous_pi fun j => ?_)
    exact continuous_const.mul (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
  have hΨchar : ∀ v j, bohrHullChar f (lam j) (Ψ v)
      = Complex.exp ((Real.pi : ℂ) * Complex.I * (v j : ℂ)) := by
    intro v j
    rw [hΨ, hφval]
    congr 1
    push_cast
    ring
  have hΨinj : Set.InjOn Ψ (unitCube r) := by
    intro v hv v' hv' heq
    refine HTGeometry.eq_of_exp_pi_mul_I_eq hv hv' fun j => ?_
    rw [← hΨchar v j, ← hΨchar v' j, heq]
  exact HTGeometry.false_of_compact_homogeneous_embedding J hJc hJi
    (homogeneous_bohrHull f) (isOpen_openUnitCube r) (openUnitCube_nonempty r)
    (hΨcont.continuousOn) (hΨinj.mono (openUnitCube_subset r))

end GaloisForLFunctions

namespace GaloisForLFunctions

open Metric Set Topology

open scoped BoundedContinuousFunction

variable {V : Type*} [NormedAddCommGroup V] {f : ℝ →ᵇ V}

/-- **The strict frequency-rank law.**  A globally injective continuous chart of the phase carrier
into `ℝ^k` bounds the rational rank of the frequency group by `k - 1`. -/
theorem rank_bohrHullFrequencies_le_pred_of_global_chart
    (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {k : ℕ} (hk : 0 < k) (J : BohrHull f → EuclideanSpace ℝ (Fin k))
    (hJc : Continuous J) (hJi : Function.Injective J) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ ((k - 1 : ℕ) : Cardinal) := by
  classical
  refine rank_le fun s hs => ?_
  set lam : (↥s) → ℝ := fun i => ((i : bohrHullFrequencies f) : ℝ) with hlamdef
  have hker : LinearMap.ker ((bohrHullFrequencies f).subtype.toIntLinearMap) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact Subtype.ext hxy
  have hZ : LinearIndependent ℤ lam := hs.map' ((bohrHullFrequencies f).subtype.toIntLinearMap) hker
  have hQ : LinearIndependent ℚ lam := (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).mp hZ
  have hfreq : ∀ i : ↥s, IsBohrHullFrequency f (lam i) :=
    fun i => mem_bohrHullFrequencies.mp (i : bohrHullFrequencies f).2
  set e : Fin (Fintype.card ↥s) ≃ ↥s := (Fintype.equivFin ↥s).symm with hedef
  have hind' : LinearIndependent ℚ (lam ∘ e) := hQ.comp e e.injective
  have hcard := card_lt_of_hull_global_chart hf htb hind' (fun i => hfreq (e i)) hk J hJc hJi
  rw [Fintype.card_coe] at hcard
  omega

end GaloisForLFunctions
