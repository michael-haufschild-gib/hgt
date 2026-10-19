import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiBooleanPrimeCube

/-!
# Native finite packets on an odd-prime Boolean cube

The injective prime-product index identifies the Boolean cube with a finite set
of literal odd integers. Transporting coefficients through this equivalence
reuses the native odd-divisor packet energy theorem: its Gram is the Boolean
kernel with exactly one global odd homogeneous mass factor.

These are finite reindexing identities supporting the dyadic-antichain
prime-capacity theorem; no new classical Gram estimate is asserted here.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

/-- Literal integer support of the squarefree prime cube, including the unit. -/
def fermiPrimeCubeSupport (P : Finset ℕ) : Finset ℕ :=
  Finset.univ.image (fermiPrimeCubeIndex P)

/-- Unique prime factorization identifies cube coordinates with their integer support. -/
def fermiPrimeCubeEquiv (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (P → Bool) ≃ fermiPrimeCubeSupport P :=
  Equiv.ofBijective
    (fun x => ⟨fermiPrimeCubeIndex P x, Finset.mem_image.mpr ⟨x, mem_univ _, rfl⟩⟩)
    ⟨fun x y h => fermiPrimeCubeIndex_injective P hP (congrArg Subtype.val h),
      fun d => by
        obtain ⟨x, _, hx⟩ := Finset.mem_image.mp d.2
        exact ⟨x, Subtype.ext hx⟩⟩

/-- The support equivalence preserves the literal arithmetic index. -/
@[simp] theorem fermiPrimeCubeEquiv_coe (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (x : P → Bool) :
    ((fermiPrimeCubeEquiv P hP x : fermiPrimeCubeSupport P) : ℕ) =
      fermiPrimeCubeIndex P x := rfl

/-- Every cube index is odd when all generating primes are odd. -/
theorem fermiPrimeCubeSupport_odd (P : Finset ℕ) (hodd : ∀ p ∈ P, Odd p) :
    ∀ d ∈ fermiPrimeCubeSupport P, Odd d := by
  intro d hd
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
  exact fermiPrimeCubeIndex_odd P hodd x

/-- Transport a native divisor packet to its Boolean coefficient coordinates. -/
theorem fermiPrimeCubePacket_reindex (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (f : (P → Bool) → ℝ) (m : ℕ) :
    fermiOddDivisorPacket (fermiPrimeCubeSupport P)
      (fun d => f ((fermiPrimeCubeEquiv P hP).symm d)) m =
      ∑ x : P → Bool, f x * fermiOddDivisorProfile (fermiPrimeCubeIndex P x) m := by
  unfold fermiOddDivisorPacket
  simpa using ((fermiPrimeCubeEquiv P hP).sum_comp
    (fun d => f ((fermiPrimeCubeEquiv P hP).symm d) *
      fermiOddDivisorProfile d m)).symm

/-- Exact native packet energy, with one global odd mass and the Boolean Gram form. -/
theorem fermiPrimeCubePacket_energy (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (f : (P → Bool) → ℝ) :
    Summable (fun m : ℕ => (fermiOddDivisorPacket (fermiPrimeCubeSupport P)
      (fun d => f ((fermiPrimeCubeEquiv P hP).symm d)) m)^2) ∧
    (∑' m : ℕ, (fermiOddDivisorPacket (fermiPrimeCubeSupport P)
      (fun d => f ((fermiPrimeCubeEquiv P hP).symm d)) m)^2) =
      fermiOddHomogeneousMass * fermiBooleanGramForm (fun p : P => 1 / (p : ℝ)) f f := by
  let e := fermiPrimeCubeEquiv P hP
  obtain ⟨hs, he⟩ := fermiOddDivisorPacket_energy (fermiPrimeCubeSupport P)
    (fermiPrimeCubeSupport_odd P hodd) (fun d => f (e.symm d))
  refine ⟨hs, he.trans ?_⟩
  congr 1
  unfold fermiBooleanGramForm
  rw [← e.sum_comp (fun d => ∑ t : fermiPrimeCubeSupport P,
    gcdSquareRatioMatrix (fermiPrimeCubeSupport P) d t * f (e.symm d) * f (e.symm t))]
  apply Finset.sum_congr rfl
  intro x _
  rw [← e.sum_comp (fun t => gcdSquareRatioMatrix (fermiPrimeCubeSupport P) (e x) t *
    f (e.symm (e x)) * f (e.symm t))]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Equiv.symm_apply_apply, gcdSquareRatioMatrix, e, fermiPrimeCubeEquiv_coe]
  rw [fermiPrimeCubeIndex_gcd_gram P hP]
  ring

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
