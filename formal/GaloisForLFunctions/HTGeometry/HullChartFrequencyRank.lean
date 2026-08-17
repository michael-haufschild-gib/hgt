import GaloisForLFunctions.HTGeometry.BohrHullParameterSubgroup
import GaloisForLFunctions.HTGeometry.CubeChartDimension
import GaloisForLFunctions.HTGeometry.CircleCoordinateCube

/-!
# Frequency rank from a finite atlas of local charts

The frequency-rank bound needs no global embedding of the phase carrier: a finite closed cover on
each piece of which some continuous map to `ℝ^k` is injective already forces the rational rank of
the frequency group to be at most `k`.

The independent packet turns the cube into the carrier through the parameter subgroup, injectively
because the characters separate its points; the cover pulls back to a finite closed cover of the
cube by chart domains, and Baire inside the cube produces one chart containing a full affine copy of
the cube.

This is the step that removes the hypothesis of a *single* regular chart: a differential equation
whose separant vanishes somewhere still has, by compactness, a finite atlas of regular charts, and
that is enough.
-/

namespace GaloisForLFunctions

open Metric Set

open scoped BoundedContinuousFunction

variable {f : ℝ →ᵇ ℂ}

/-- **An independent frequency packet is bounded by the dimension of a finite chart atlas.** -/
theorem card_le_of_hull_charts (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {r : ℕ} {lam : Fin r → ℝ} (hind : LinearIndependent ℚ lam)
    (hlam : ∀ j, IsBohrHullFrequency f (lam j))
    {N k : ℕ} (F : Fin N → Set (BohrHull f)) (hFclosed : ∀ j, IsClosed (F j))
    (hcover : ∀ x : BohrHull f, ∃ j, x ∈ F j)
    (E : Fin N → BohrHull f → EuclideanSpace ℝ (Fin k))
    (hEcont : ∀ j, ContinuousOn (E j) (F j))
    (hEinj : ∀ j, Set.InjOn (E j) (F j)) : r ≤ k := by
  classical
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
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
  refine HTGeometry.le_of_unitCube_charts (fun j => Ψ ⁻¹' F j)
    (fun j => (hFclosed j).preimage hΨcont) (fun x _ => hcover (Ψ x))
    (fun j v => E j (Ψ v)) ?_ ?_
  · intro j
    exact (hEcont j).comp hΨcont.continuousOn fun v hv => hv.1
  · intro j v hv v' hv' heq
    exact hΨinj hv.2 hv'.2 (hEinj j hv.1 hv'.1 heq)

/-- **The rational rank of the frequency group is bounded by the chart dimension.** -/
theorem rank_bohrHullFrequencies_le_of_charts (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {N k : ℕ} (F : Fin N → Set (BohrHull f)) (hFclosed : ∀ j, IsClosed (F j))
    (hcover : ∀ x : BohrHull f, ∃ j, x ∈ F j)
    (E : Fin N → BohrHull f → EuclideanSpace ℝ (Fin k))
    (hEcont : ∀ j, ContinuousOn (E j) (F j))
    (hEinj : ∀ j, Set.InjOn (E j) (F j)) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ (k : Cardinal) := by
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
  have hcard := card_le_of_hull_charts hf htb hind' (fun i => hfreq (e i)) F hFclosed hcover E
    hEcont hEinj
  rwa [Fintype.card_coe] at hcard

end GaloisForLFunctions
