import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiBooleanPrimeCubePackets
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiBankParityTensorGram

/-!
# Literal odd integers on finitely many disjoint prime banks

Independent Boolean choices in finitely many pairwise disjoint banks of primes
multiply to one literal squarefree integer. Each bank prime has exponent equal
to its Boolean coordinate, so the index is injective, and for odd banks it is odd.
By unique factorization, the normalized arithmetic GCD kernel of two such
indices is the product of the single-bank Boolean kernels. Transporting native
odd-divisor packets through the resulting finite equivalence gives their exact
energy: one global odd reciprocal-square mass times the product-kernel form.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

variable {I : Type*} [Fintype I]

/-- The squarefree integer of independent Boolean prime choices in several banks. -/
def fermiBankCubeIndex (T : I → Finset ℕ) (x : ∀ i, T i → Bool) : ℕ :=
  ∏ i, fermiPrimeCubeIndex (T i) (x i)

theorem fermiBankCubeIndex_pos (T : I → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    (x : ∀ i, T i → Bool) : 0 < fermiBankCubeIndex T x :=
  Finset.prod_pos (fun i _ => fermiPrimeCubeIndex_pos (T i) (hT i) (x i))

theorem fermiBankCubeIndex_odd (T : I → Finset ℕ) (hodd : ∀ i, ∀ p ∈ T i, Odd p)
    (x : ∀ i, T i → Bool) : Odd (fermiBankCubeIndex T x) :=
  Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) (by decide : Odd (1 : ℕ))
    (fun i _ => fermiPrimeCubeIndex_odd (T i) (hodd i) (x i))

/-- Every prime factor of a bank-cube index lies in one of the banks. -/
theorem fermiBankCubeIndex_primeFactors (T : I → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    (x : ∀ i, T i → Bool) :
    ∀ p ∈ (fermiBankCubeIndex T x).primeFactors, ∃ i, p ∈ T i := by
  intro p hp
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hdvd
  exact ⟨i, fermiPrimeCubeIndex_primeFactors_subset (T i) (hT i) (x i)
    (Nat.mem_primeFactors.mpr ⟨hpp, hi, (fermiPrimeCubeIndex_pos (T i) (hT i) (x i)).ne'⟩)⟩

/-- Each bank prime occurs with exponent equal to its Boolean coordinate. -/
theorem fermiBankCubeIndex_factorization (T : I → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    (hdisj : Pairwise (fun i k => Disjoint (T i) (T k))) (x : ∀ i, T i → Bool)
    (i : I) (p : T i) :
    (fermiBankCubeIndex T x).factorization p = if x i p then 1 else 0 := by
  unfold fermiBankCubeIndex
  rw [Nat.factorization_prod (fun k _ => (fermiPrimeCubeIndex_pos (T k) (hT k) (x k)).ne'),
    Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · exact fermiPrimeCubeIndex_factorization (T i) (hT i) (x i) p
  · intro k _ hki
    apply Finsupp.notMem_support_iff.mp
    rw [Nat.support_factorization]
    intro hp
    exact Finset.disjoint_left.mp (hdisj hki)
      (fermiPrimeCubeIndex_primeFactors_subset (T k) (hT k) (x k) hp) p.2
  · intro h
    exact (h (Finset.mem_univ i)).elim

theorem fermiBankCubeIndex_injective (T : I → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    (hdisj : Pairwise (fun i k => Disjoint (T i) (T k))) :
    Function.Injective (fermiBankCubeIndex T) := by
  intro x y hxy
  funext i p
  have h := congrArg (fun n : ℕ => n.factorization p) hxy
  simp only [fermiBankCubeIndex_factorization T hT hdisj] at h
  cases hx : x i p <;> cases hy : y i p <;> simp_all

/-- The normalized GCD kernel of bank-cube indices is the product of bank kernels. -/
theorem fermiBankCubeIndex_gcd_gram (T : I → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    (hdisj : Pairwise (fun i k => Disjoint (T i) (T k))) (x y : ∀ i, T i → Bool) :
    (Nat.gcd (fermiBankCubeIndex T x) (fermiBankCubeIndex T y) : ℝ)^2 /
      ((fermiBankCubeIndex T x : ℝ) * (fermiBankCubeIndex T y : ℝ)) =
      ∏ i, fermiBooleanGram (fun p : T i => 1 / (p : ℝ)) (x i) (y i) := by
  let P := Finset.univ.biUnion T
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hp
    exact hT i p hi
  have hsub (z : ∀ i, T i → Bool) : (fermiBankCubeIndex T z).primeFactors ⊆ P := by
    intro p hp
    obtain ⟨i, hi⟩ := fermiBankCubeIndex_primeFactors T hT z p hp
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
  rw [gcdSquareRatio_eq_primeProduct P hP (fermiBankCubeIndex_pos T hT x).ne'
    (fermiBankCubeIndex_pos T hT y).ne' (hsub x) (hsub y),
    Finset.prod_biUnion (fun i _ k _ hik => hdisj hik)]
  apply Finset.prod_congr rfl
  intro i _
  unfold fermiBooleanGram
  rw [← Finset.prod_coe_sort (T i) (fun p => (1 / (p : ℝ)) ^
    (((fermiBankCubeIndex T x).factorization p - (fermiBankCubeIndex T y).factorization p) +
      ((fermiBankCubeIndex T y).factorization p - (fermiBankCubeIndex T x).factorization p)))]
  apply Finset.prod_congr rfl
  intro p _
  rw [fermiBankCubeIndex_factorization T hT hdisj x i p,
    fermiBankCubeIndex_factorization T hT hdisj y i p]
  cases x i p <;> cases y i p <;> norm_num

variable [DecidableEq I]

/-- Literal integer support of the multi-bank cube. -/
def fermiBankCubeSupport (T : I → Finset ℕ) : Finset ℕ :=
  Finset.univ.image (fermiBankCubeIndex T)

/-- Unique factorization identifies multi-bank coordinates with their integer support. -/
def fermiBankCubeEquiv (T : I → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    (hdisj : Pairwise (fun i k => Disjoint (T i) (T k))) :
    (∀ i, T i → Bool) ≃ fermiBankCubeSupport T :=
  Equiv.ofBijective
    (fun x => ⟨fermiBankCubeIndex T x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun x y h => fermiBankCubeIndex_injective T hT hdisj (congrArg Subtype.val h),
      fun d => by
        obtain ⟨x, _, hx⟩ := Finset.mem_image.mp d.2
        exact ⟨x, Subtype.ext hx⟩⟩

@[simp] theorem fermiBankCubeEquiv_coe (T : I → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    (hdisj : Pairwise (fun i k => Disjoint (T i) (T k))) (x : ∀ i, T i → Bool) :
    ((fermiBankCubeEquiv T hT hdisj x : fermiBankCubeSupport T) : ℕ) =
      fermiBankCubeIndex T x := rfl

theorem fermiBankCubeSupport_odd (T : I → Finset ℕ) (hodd : ∀ i, ∀ p ∈ T i, Odd p) :
    ∀ d ∈ fermiBankCubeSupport T, Odd d := by
  intro d hd
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
  exact fermiBankCubeIndex_odd T hodd x

theorem fermiBankCubeSupport_primeFactors (T : I → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime) :
    ∀ d ∈ fermiBankCubeSupport T, ∀ p ∈ d.primeFactors, ∃ i, p ∈ T i := by
  intro d hd
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
  exact fermiBankCubeIndex_primeFactors T hT x

/-- Exact native packet energy on the multi-bank cube, with one global odd mass. -/
theorem fermiBankCubePacket_energy (T : I → Finset ℕ) (hT : ∀ i, ∀ p ∈ T i, p.Prime)
    (hodd : ∀ i, ∀ p ∈ T i, Odd p) (hdisj : Pairwise (fun i k => Disjoint (T i) (T k)))
    (f : (∀ i, T i → Bool) → ℝ) :
    Summable (fun m : ℕ => (fermiOddDivisorPacket (fermiBankCubeSupport T)
      (fun d => f ((fermiBankCubeEquiv T hT hdisj).symm d)) m)^2) ∧
    (∑' m : ℕ, (fermiOddDivisorPacket (fermiBankCubeSupport T)
      (fun d => f ((fermiBankCubeEquiv T hT hdisj).symm d)) m)^2) =
      fermiOddHomogeneousMass * ∑ x : ∀ i, T i → Bool, ∑ y : ∀ i, T i → Bool,
        f x * (∏ i, fermiBooleanGram (fun p : T i => 1 / (p : ℝ)) (x i) (y i)) * f y := by
  let e := fermiBankCubeEquiv T hT hdisj
  obtain ⟨hs, he⟩ := fermiOddDivisorPacket_energy (fermiBankCubeSupport T)
    (fermiBankCubeSupport_odd T hodd) (fun d => f (e.symm d))
  refine ⟨hs, he.trans ?_⟩
  congr 1
  rw [← e.sum_comp (fun d => ∑ t : fermiBankCubeSupport T,
    gcdSquareRatioMatrix (fermiBankCubeSupport T) d t * f (e.symm d) * f (e.symm t))]
  apply Finset.sum_congr rfl
  intro x _
  rw [← e.sum_comp (fun t => gcdSquareRatioMatrix (fermiBankCubeSupport T) (e x) t *
    f (e.symm (e x)) * f (e.symm t))]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Equiv.symm_apply_apply, gcdSquareRatioMatrix, e, fermiBankCubeEquiv_coe]
  rw [fermiBankCubeIndex_gcd_gram T hT hdisj]
  ring

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
