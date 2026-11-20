import GaloisForLFunctions.ExceptionalLayerTheory.TheHighDerivativeAreasOfAWholeObservationDisk
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Counting distinct zeros with an absolute error tolerance

In a disk of winding W, one normalized derivative-area reading of order
8W+1 eventually counts distinct zeros after rounding, even with an
additional absolute measurement error up to 1/4. As derivative order
tends to infinity, the first correction to the count records the product
of the multiplicities.
-/

noncomputable section
open Complex Filter Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The finite Mellin sum of positive orders interpolates all normalized
derivative-area limits of a disk. -/
def zeroOrderMellinSum {ι : Type*} (S : Finset ι) (m : ι → ℕ) (q : ℝ) :=
  ∑ i ∈ S, (m i:ℝ)^q

theorem distinct_count_area_bounds {ι : Type*} (S : Finset ι) (m : ι → ℕ)
    (hm : ∀ i ∈ S, 0 < m i) {q : ℝ} (hq : 0≤q) (hq' : q≤1) :
    (S.card:ℝ) ≤ zeroOrderMellinSum S m q ∧
    zeroOrderMellinSum S m q ≤ S.card+q*((∑ i ∈ S, (m i:ℝ))-S.card) := by
  have h₁ (i : ι) (hi : i∈S) : (1:ℝ)≤m i := by exact_mod_cast hm i hi
  constructor
  · simpa [zeroOrderMellinSum] using Finset.sum_le_sum
      (fun i hi => Real.one_le_rpow (h₁ i hi) hq)
  · have hsum := Finset.sum_le_sum (s:=S) (f:=fun i => (m i:ℝ)^q)
      (g:=fun i => 1+q*((m i:ℝ)-1)) (fun i hi => by
        have h := rpow_one_add_le_one_add_mul_self (s:=(m i:ℝ)-1)
          (by linarith only [h₁ i hi]) hq hq'
        rwa [show 1+((m i:ℝ)-1)=(m i:ℝ) by ring] at h)
    simpa [zeroOrderMellinSum,Finset.sum_add_distrib,←Finset.mul_sum,
      Finset.sum_sub_distrib] using hsum

/-- The first order correction as the Mellin exponent tends to zero
is the logarithm of the product of the positive multiplicities. -/
theorem log_product_from_order_areas {ι : Type*} (S : Finset ι) (m : ι → ℕ)
    (hm : ∀ i ∈ S, 0 < m i) :
    Tendsto (fun q : ℝ => (zeroOrderMellinSum S m q-S.card)/q) (𝓝[≠] 0)
      (𝓝 (Real.log (∏ i ∈ S, (m i:ℝ)))) := by
  have hterm (i : ι) (hi : i∈S) :
      HasDerivAt (fun q : ℝ => (m i:ℝ)^q) (Real.log (m i:ℝ)) 0 := by
    simpa only [id_eq,Real.rpow_zero,mul_one] using
      ((hasDerivAt_id (0:ℝ)).const_rpow (Nat.cast_pos.mpr (hm i hi) : (0:ℝ) < m i))
  have h := (HasDerivAt.fun_sum hterm).tendsto_slope_zero
  rw [Real.log_prod (fun i hi => (Nat.cast_pos.mpr (hm i hi) : (0:ℝ) < m i).ne')]
  simpa [zeroOrderMellinSum,div_eq_inv_mul] using h

/-- A single finite-order reading on any regular circle counts its
distinct ξ-zeros with a fixed absolute noise tolerance, including at
winding zero. The derivative order uses only the winding. -/
theorem robust_count_of_distinct_xi_zeros (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    let W := (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat
    ∃ t : Finset ℂ, (∀ z, z∈t ↔ ‖z-c‖<R ∧ xi z=0) ∧
      ∀ᶠ u : ℝ in atTop, ∀ e : ℝ, |e|≤1/4 →
        ⌊xiDerivativeDiskArea (8*W+1) c R u+e+1/2⌋ = (t.card:ℤ) := by
  classical
  obtain ⟨t,ht,hw,ha⟩ := xi_disk_fractional_moments c hR hb
  let W := ∑ z ∈ t, hadamardOrder z
  have hW : (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat=W := by
    rw [hw,←Nat.cast_sum,Int.toNat_natCast]
  dsimp only
  rw [hW]
  refine ⟨t,ht,?_⟩
  let j := 8*W+1
  let q := 2/((j+1:ℕ):ℝ)
  have hd : ((j+1:ℕ):ℝ)=8*(W:ℝ)+2 := by push_cast [j]; ring
  have hden : 0<((j+1:ℕ):ℝ) := by positivity
  have hq : 0<q := div_pos (by norm_num) hden
  have hq' : q≤1 := (div_le_iff₀ hden).mpr (by rw [hd,one_mul]; linarith only [Nat.cast_nonneg (R:=ℝ) W])
  have hqW : q*(W:ℝ)<1/4 := by
    change (2/_)*(W:ℝ)<_
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).mpr
    rw [hd]
    linarith only
  have hm (z : ℂ) (hz : z∈t) : 0<hadamardOrder z := Nat.pos_of_ne_zero
    (fun hn => (hadamardOrder_zero_iff z).mp hn ((ht z).mp hz).2)
  obtain ⟨hlo,hhi⟩ := distinct_count_area_bounds t hadamardOrder hm hq.le hq'
  have hcast : ∑ z ∈ t, (hadamardOrder z:ℝ)=(W:ℝ) := by simp [W]
  rw [hcast] at hhi
  have hup : zeroOrderMellinSum t hadamardOrder q < (t.card:ℝ)+1/4 := by
    have hle := mul_le_mul_of_nonneg_left (sub_le_self (W:ℝ) (Nat.cast_nonneg t.card)) hq.le
    linarith only [hhi,hle,hqW]
  have hl : Tendsto (xiDerivativeDiskArea j c R) atTop (𝓝 (zeroOrderMellinSum t hadamardOrder q)) := ha j
  filter_upwards [hl.eventually_lt_const hup,
    hl.eventually_const_lt (show (t.card:ℝ)-1/4<zeroOrderMellinSum t hadamardOrder q by
      linarith only [hlo])] with u hu hlower
  intro e he
  obtain ⟨he₁,he₂⟩ := abs_le.mp he
  apply Int.floor_eq_iff.mpr
  simp only [Int.cast_natCast]
  change (t.card:ℝ) ≤ xiDerivativeDiskArea j c R u+e+1/2 ∧ _
  constructor <;> linarith only [hu,hlower,he₁,he₂]

#print axioms distinct_count_area_bounds
#print axioms log_product_from_order_areas
#print axioms robust_count_of_distinct_xi_zeros
end GaloisForLFunctions.ExceptionalLayerTheory
