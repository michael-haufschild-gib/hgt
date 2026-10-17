import GaloisForLFunctions.BiScaleUncertainty.SharedOriginMultiCosetLeverage
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported

open MeasureTheory Set
open scoped BigOperators CompactlySupported Convolution
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

/-- Dyadic depth of the logarithmic node indexed by k, namely k+2. -/
def logNodeDyadicDepth (k : ℕ) : ℕ :=
  (Nat.exists_eq_two_pow_mul_odd (n := k + 2) (by omega)).choose

/-- Odd part of the logarithmic node k+2. -/
def logNodeOddPart (k : ℕ) : ℕ :=
  (Nat.exists_eq_two_pow_mul_odd (n := k + 2) (by omega)).choose_spec.choose

theorem logNode_oddPart_factorization (k : ℕ) :
    Odd (logNodeOddPart k) ∧ k + 2 = 2 ^ logNodeDyadicDepth k * logNodeOddPart k :=
  (Nat.exists_eq_two_pow_mul_odd (n := k + 2) (by omega)).choose_spec.choose_spec

/-- Nodes in one odd fibre are comparable by divisibility. -/
theorem logNode_oddPart_comparable {i j : ℕ} (hij : logNodeOddPart i = logNodeOddPart j) :
    (i + 2) ∣ (j + 2) ∨ (j + 2) ∣ (i + 2) := by
  have hi := (logNode_oddPart_factorization i).2
  have hj := (logNode_oddPart_factorization j).2
  rw [hi, hj, hij]
  rcases le_total (logNodeDyadicDepth i) (logNodeDyadicDepth j) with h | h
  · exact Or.inl (Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 h) _)
  · exact Or.inr (Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 h) _)

/-- The nonempty set of odd cosets meeting nodes 2 through n+2. -/
def logarithmicOddCosets (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).image logNodeOddPart

/-- The complete finite fibre of one odd coset. -/
def logarithmicCosetNodes (n m : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k => logNodeOddPart k = m)

theorem logarithmicOddCosets_nonempty (n : ℕ) : (logarithmicOddCosets n).Nonempty := by
  exact ⟨logNodeOddPart 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩

/-- Grouping all grid nodes by their odd part neither omits nor repeats a node. -/
theorem sum_logarithmicCosetNodes {α : Type*} [AddCommMonoid α] (n : ℕ) (v : ℕ → α) :
    (∑ m ∈ logarithmicOddCosets n, ∑ k ∈ logarithmicCosetNodes n m, v k) =
      ∑ k ∈ Finset.range (n + 1), v k := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun k hk => Finset.mem_image.mpr ⟨k, hk, rfl⟩) v

/-- A sign chooses the right or left collar offset. -/
def collarSignedOffset (σ : Bool) (y : ℝ) : ℝ := if σ then y else -y

/-- The signed coset index set shares a single origin coordinate. -/
def logarithmicSignedCosets (n : ℕ) : Finset (ℕ × Bool) :=
  (logarithmicOddCosets n) ×ˢ Finset.univ

theorem logarithmicSignedCosets_nonempty (n : ℕ) : (logarithmicSignedCosets n).Nonempty := by
  obtain ⟨m, hm⟩ := logarithmicOddCosets_nonempty n
  exact ⟨(m, false), Finset.mem_product.mpr ⟨hm, Finset.mem_univ _⟩⟩

/-- Signed coset summation is exactly the sum of both collar signs at every node. -/
theorem sum_logarithmicSignedCosets {α : Type*} [AddCommMonoid α]
    (n : ℕ) (v : Bool → ℕ → α) :
    (∑ j ∈ logarithmicSignedCosets n, ∑ k ∈ logarithmicCosetNodes n j.1, v j.2 k) =
      ∑ k ∈ Finset.range (n + 1), (v false k + v true k) := by
  simp only [logarithmicSignedCosets, Finset.sum_product, Fintype.sum_bool,
    Finset.sum_add_distrib, sum_logarithmicCosetNodes]
  exact add_comm _ _

/-- Literal signed odd-coset spheres follow from the grid zeros alone. -/
theorem autocorr_logarithmicCoset_sphere (f : C_c(ℝ, ℝ)) (n m : ℕ)
    (hgrid : ∀ k ∈ Finset.range (n + 1), autocorr f (Real.log ((k + 2 : ℕ) : ℝ)) = 0)
    (σ : Bool) (y : ℝ) :
    autocorr f y ^ 2 +
      (∑ k ∈ logarithmicCosetNodes n m,
        autocorr f (Real.log ((k + 2 : ℕ) : ℝ) + collarSignedOffset σ y) ^ 2) ≤
      autocorr f 0 ^ 2 := by
  have hzero : ∀ k ∈ logarithmicCosetNodes n m,
      autocorr f (Real.log ((k + 2 : ℕ) : ℝ)) = 0 :=
    fun k hk => hgrid k (Finset.mem_filter.mp hk).1
  have horth : ∀ i ∈ logarithmicCosetNodes n m, ∀ j ∈ logarithmicCosetNodes n m,
      i ≠ j → autocorr f (Real.log ((i + 2 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ)) = 0 := by
    intro i hi j hj hij
    have hri := (Finset.mem_filter.mp hi).1
    have hrj := (Finset.mem_filter.mp hj).1
    have hg : ∀ a ∈ Finset.Icc 2 (n + 2), autocorr f (Real.log (a : ℝ)) = 0 := by
      intro a ha
      have hab := Finset.mem_Icc.mp ha
      have heq : a - 2 + 2 = a := Nat.sub_add_cancel hab.1
      have hx := hgrid (a - 2) (by simp only [Finset.mem_range]; omega)
      rwa [heq] at hx
    have hcmp := logNode_oddPart_comparable
      ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    apply autocorr_log_divisibility_pair_orth hg (by omega) (by omega)
      (by simp only [Finset.mem_range] at hri; omega)
      (by simp only [Finset.mem_range] at hrj; omega)
    rcases hcmp with hdiv | hdiv
    · exact Or.inl ⟨lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdiv) (by omega), hdiv⟩
    · exact Or.inr ⟨lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdiv) (by omega), hdiv⟩
  cases σ with
  | false =>
      simpa only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg] using
        autocorr_origin_chain_sphere_sub_le f.hasCompactSupport f.continuous
          (logarithmicCosetNodes n m) (fun k => Real.log ((k + 2 : ℕ) : ℝ)) hzero horth y
  | true =>
      simpa only [collarSignedOffset, ↓reduceIte] using
        autocorr_origin_chain_sphere_add_le f.hasCompactSupport f.continuous
          (logarithmicCosetNodes n m) (fun k => Real.log ((k + 2 : ℕ) : ℝ)) hzero horth y

/-- Continuity of autocorrelation needs no differentiability assumption. -/
theorem continuous_autocorr_compact (f : C_c(ℝ, ℝ)) : Continuous (autocorr f) := by
  have hc := (f.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)).continuous_convolution_right (μ := volume)
    (ContinuousLinearMap.mul ℝ ℝ) f.continuous.locallyIntegrable
    (f.continuous.comp continuous_neg)
  have heq : autocorr f = fun x =>
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun u => f (-u))) (-x) := by
    funext x
    unfold autocorr convolution
    simp only [ContinuousLinearMap.mul_apply']
    congr 1
    funext u
    congr 1
    congr 1
    ring
  rw [heq]
  exact hc.comp continuous_neg

/-- Autocorrelation as a continuous kernel. -/
def compactAutocorrKernel (f : C_c(ℝ, ℝ)) : C(ℝ, ℝ) :=
  ⟨autocorr f, continuous_autocorr_compact f⟩

end
end GaloisForLFunctions.BiScaleUncertainty
