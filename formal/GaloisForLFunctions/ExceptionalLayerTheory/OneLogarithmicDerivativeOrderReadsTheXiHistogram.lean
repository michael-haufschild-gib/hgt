import GaloisForLFunctions.ExceptionalLayerTheory.OneHighDerivativeAreaDeterminesTheWholeMultiplicityHistogram
import GaloisForLFunctions.ExceptionalLayerTheory.PrimeRadicalWeightsOfTheDerivativeAreas
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Log

/-!
# One explicitly bounded derivative order reads the ξ histogram

Choose a prime p with 2^p greater than the winding. The derivative of
order 2p−1 measures the sum of the real p-th roots of the multiplicities.
Their rational independence separates every histogram on the allowed
orders. Bertrand's postulate gives a derivative order below four times
the larger of one and the binary logarithm of the winding.
-/

noncomputable section
open Complex Filter Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- At derivative order 2p−1 the area weight is the positive p-th root. -/
theorem prime_order_weight {p : ℕ} (hp : 0<p) (k : ℕ) :
    orderAreaWeight (2*p-1) k = ((k+1:ℕ):ℝ)^((p:ℝ)⁻¹) := by
  have he : 2*p-1+1=2*p := by omega
  rw [orderAreaWeight,he,Nat.cast_mul,Nat.cast_ofNat]
  congr 1
  field_simp [Nat.cast_ne_zero.mpr hp.ne' : (p:ℝ)≠0]

/-- Rational histogram coefficients of any size are distinguished
by this single order whenever all candidate multiplicities are below 2^p. -/
theorem prime_derivative_area_injective {W p : ℕ} (hp : p.Prime) (hW : W<2^p) :
    Function.Injective (fun a : Fin W → ℚ => divisorAreaMoment (2*p-1) (fun k => (a k:ℝ))) := by
  intro a b he
  unfold divisorAreaMoment at he
  rw [←sub_eq_zero,←Finset.sum_sub_distrib] at he
  have hr : ∑ i : Fin W, (a i-b i) • (((i.val+1:ℕ):ℝ)^((p:ℝ)⁻¹))=0 := by
    simpa only [prime_order_weight hp.pos,←mul_sub,Rat.smul_def,Rat.cast_sub,mul_comm] using he
  funext i
  exact sub_eq_zero.mp (linearIndependent_iff'.mp (independent_prime_radical_weights hp hW)
    Finset.univ (fun k => a k-b k) hr i (Finset.mem_univ _))

/-- There exists a prime calibration of order below the stated binary
logarithmic bound, including zero and unit winding. -/
theorem exists_logarithmic_prime_calibration (W : ℕ) :
    ∃ p : ℕ, p.Prime ∧ W<2^p ∧ 2*p-1<4*max 1 (Nat.log 2 W) := by
  let n := max 1 (Nat.log 2 W)
  have hn : 0<n := zero_lt_one.trans_le (le_max_left ..)
  obtain ⟨p,hp,hl,hu⟩ := Nat.exists_prime_lt_and_le_two_mul n hn.ne'
  refine ⟨p,hp,Nat.lt_pow_of_log_lt (by decide : 1<2) ((le_max_right ..).trans_lt hl),?_⟩
  change 2*p-1<4*n
  omega

/-- One area measured over the whole disk eventually identifies every
enclosed multiplicity by its nearest integer-histogram prediction.
The chosen order depends only on the winding, with a logarithmic bound. -/
theorem logarithmic_order_decodes_the_xi_divisor (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    let W := (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat
    ∃ p : ℕ, p.Prime ∧ W<2^p ∧ 2*p-1<4*max 1 (Nat.log 2 W) ∧
      ∃ t : Finset ℂ, (∀ z, z∈t ↔ ‖z-c‖<R ∧ xi z=0) ∧
        ∀ᶠ u : ℝ in atTop, ∀ b : BoundedOrderCounts W,
          (∀ e : BoundedOrderCounts W,
            |xiDerivativeDiskArea (2*p-1) c R u-boundedOrderMoment (2*p-1) b|≤
            |xiDerivativeDiskArea (2*p-1) c R u-boundedOrderMoment (2*p-1) e|) ↔
            ∀ k, (b k).val=divisorOrderCounts t W k := by
  dsimp only
  let W := (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat
  obtain ⟨p,hp,hW,hj⟩ := exists_logarithmic_prime_calibration W
  obtain ⟨t,ht,hcap,ha⟩ := xi_disk_bounded_order_counts c hR hb
  let a : BoundedOrderCounts W := fun k => ⟨divisorOrderCounts t W k,Nat.lt_succ_of_le (hcap k)⟩
  have hinj : Function.Injective (boundedOrderMoment (W:=W) (2*p-1)) := by
    intro b e h
    have hq : (fun i => ((b i).val:ℚ))=(fun i => ((e i).val:ℚ)) :=
      prime_derivative_area_injective hp hW (by simpa only [Rat.cast_natCast] using h)
    funext i
    exact Fin.ext (by exact_mod_cast congrFun hq i)
  refine ⟨p,hp,hW,hj,t,ht,?_⟩
  have hl : Tendsto (xiDerivativeDiskArea (2*p-1) c R) atTop (𝓝 (boundedOrderMoment (2*p-1) a)) := ha _
  filter_upwards [nearest_finite_observation hinj hl] with u hu b
  rw [hu]
  exact ⟨fun he k => congrArg Fin.val (congrFun he k),fun he => funext fun k => Fin.ext (he k)⟩

#print axioms prime_derivative_area_injective
#print axioms logarithmic_order_decodes_the_xi_divisor
end GaloisForLFunctions.ExceptionalLayerTheory
