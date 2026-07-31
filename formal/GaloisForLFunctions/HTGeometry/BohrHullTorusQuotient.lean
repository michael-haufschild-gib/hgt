import GaloisForLFunctions.HTGeometry.BohrHullCharacter

/-!
# The phase carrier surjects onto the torus of any independent frequency packet

If finitely many Bohr frequencies of `f` are linearly independent over `ℚ`, the characters they
determine on the Bohr hull of `f` realize *every* point of the corresponding torus.

The proof needs no duality theorem.  The joint character map is a continuous map from a compact
group, so its range is closed; Kronecker's approximation theorem puts the image of the real line
densely into the torus; hence the range contains the whole torus.

This is the carrier statement of the finite-phase law in its positive direction: an independent
packet of `r` frequencies forces the compact abelian phase carrier to cover the full `r`-torus.
-/

open Filter Topology Metric

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

variable {f : ℝ →ᵇ ℂ}

/-- The joint character map attached to a finite frequency packet. -/
def bohrHullCharPacket (f : ℝ →ᵇ ℂ) {ι : Type*} (lam : ι → ℝ) (x : BohrHull f) : ι → ℂ :=
  fun j => bohrHullChar f (lam j) x

theorem continuous_bohrHullCharPacket (f : ℝ →ᵇ ℂ) {ι : Type*} [Fintype ι] (lam : ι → ℝ) :
    Continuous (bohrHullCharPacket f lam) :=
  continuous_pi fun j => continuous_bohrHullChar f (lam j)

theorem bohrHullCharPacket_bohrIota (hfa : HTGeometry.IsBohrAlmostPeriodic (fun x => f x))
    {ι : Type*} {lam : ι → ℝ} (hne : ∀ j, bohrCoefficient (fun x => f x) (lam j) ≠ 0) (t : ℝ) :
    bohrHullCharPacket f lam (bohrIota f t) = fun j => expChar (lam j) t := by
  funext j
  exact bohrHullChar_bohrIota hfa (hne j) t

/-- **The phase carrier covers the torus of an independent frequency packet.** -/
theorem exists_bohrHull_charPacket_eq (hfa : HTGeometry.IsBohrAlmostPeriodic (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] {lam : ι → ℝ} (hind : LinearIndependent ℚ lam)
    (hne : ∀ j, bohrCoefficient (fun x => f x) (lam j) ≠ 0) (θ : ι → ℝ) :
    ∃ x : BohrHull f, ∀ j : ι,
      bohrHullChar f (lam j) x = Complex.exp ((θ j : ℝ) * Complex.I) := by
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  set y : ι → ℂ := fun j => Complex.exp ((θ j : ℝ) * Complex.I) with hy
  have hcont : Continuous (bohrHullCharPacket f lam) := continuous_bohrHullCharPacket f lam
  have hclosed : IsClosed (Set.range (bohrHullCharPacket f lam)) :=
    (isCompact_range hcont).isClosed
  have hmem : y ∈ Set.range (bohrHullCharPacket f lam) := by
    rw [← hclosed.closure_eq]
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    obtain ⟨t, ht⟩ := kronecker_approx hind θ hε
    refine ⟨bohrHullCharPacket f lam (bohrIota f t), Set.mem_range_self _, ?_⟩
    rw [dist_pi_lt_iff hε]
    intro j
    rw [bohrHullCharPacket_bohrIota hfa hne t]
    rw [dist_eq_norm, hy, norm_sub_rev]
    exact ht j
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, fun j => ?_⟩
  exact congrFun hx j

/-- The same statement with the target given by unit complex numbers. -/
theorem exists_bohrHull_charPacket_eq_of_norm_one
    (hfa : HTGeometry.IsBohrAlmostPeriodic (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    {ι : Type*} [Fintype ι] [DecidableEq ι] {lam : ι → ℝ} (hind : LinearIndependent ℚ lam)
    (hne : ∀ j, bohrCoefficient (fun x => f x) (lam j) ≠ 0) (z : ι → ℂ)
    (hz : ∀ j, ‖z j‖ = 1) :
    ∃ x : BohrHull f, ∀ j : ι, bohrHullChar f (lam j) x = z j := by
  obtain ⟨x, hx⟩ := exists_bohrHull_charPacket_eq hfa htb hind hne (fun j => (z j).arg)
  refine ⟨x, fun j => ?_⟩
  rw [hx j]
  have h := Complex.norm_mul_exp_arg_mul_I (z j)
  rw [hz j] at h
  simpa using h

end

end GaloisForLFunctions
