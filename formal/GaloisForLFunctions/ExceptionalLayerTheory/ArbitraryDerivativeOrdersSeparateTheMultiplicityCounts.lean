import GaloisForLFunctions.ExceptionalLayerTheory.TheHighDerivativeAreasOfAWholeObservationDisk
import GaloisForLFunctions.HTGeometry.ExponentialKernelAlternatingInertia

/-!
# Any distinct derivative orders separate bounded multiplicity counts

For a disk of winding W, choose any W distinct derivative orders. Their
whole-disk area limits form an invertible linear system for the numbers
of zeros of orders 1,…,W. Its matrix is an exponential Vandermonde with
nodes log m and exponents 2/(j+1). In particular the first W derivative
orders suffice, and replacing arbitrary missing orders preserves recovery.
-/

noncomputable section
open Complex Filter Matrix Topology RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Contribution of positive multiplicity k+1 at derivative order j. -/
def orderAreaWeight (j k : ℕ) := ((k+1:ℕ):ℝ)^(2/((j+1:ℕ):ℝ))

/-- One area predicted by a histogram with W possible multiplicities. -/
def divisorAreaMoment {W : ℕ} (j : ℕ) (a : Fin W → ℝ) : ℝ :=
  ∑ k, orderAreaWeight j k.val*a k

/-- Counts of positive multiplicities up to W in a finite site set. -/
def divisorOrderCounts (t : Finset ℂ) (W : ℕ) (k : Fin W) : ℕ :=
  (t.filter (fun z => hadamardOrder z=k.val+1)).card

def derivativeAreaMatrix {W : ℕ} (d : Fin W → ℕ) : Matrix (Fin W) (Fin W) ℝ :=
  fun i k => orderAreaWeight (d i) k.val

theorem derivative_area_matrix_nondegenerate {W : ℕ} {d : Fin W → ℕ} (hd : StrictMono d) :
    (derivativeAreaMatrix d).det≠0 := by
  let b (i : Fin W) : ℝ := 2/((d i+1:ℕ):ℝ)
  let y (k : Fin W) : ℝ := Real.log ((k.val+1:ℕ):ℝ)
  have hβ : StrictAnti b := by
    intro i j hij
    change 2/((d j+1:ℕ):ℝ) < 2/((d i+1:ℕ):ℝ)
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    exact mul_lt_mul_of_pos_left (by exact_mod_cast Nat.succ_lt_succ (hd hij)) (by norm_num)
  have hy : StrictMono y := by
    intro i j hij
    change Real.log ((i.val+1:ℕ):ℝ) < Real.log ((j.val+1:ℕ):ℝ)
    exact Real.log_lt_log (by positivity) (by exact_mod_cast Nat.succ_lt_succ (Fin.lt_def.mp hij))
  have he : derivativeAreaMatrix d =
      (HTGeometry.NavierStokesRealExponentialVandermonde.realExponentialVandermonde b y)ᵀ := by
    ext i k
    change ((k.val+1:ℕ):ℝ)^(b i)=Real.exp (b i*y k)
    rw [Real.rpow_def_of_pos (by positivity),mul_comm]
  rw [he,Matrix.det_transpose]
  exact HTGeometry.det_realExponentialVandermonde_ne_zero_of_anti hβ hy

/-- Any W distinct moments determine every coefficient, even for signed
real histograms. -/
theorem divisor_area_moments_injective {W : ℕ} {d : Fin W → ℕ} (hd : StrictMono d) :
    Function.Injective (fun a : Fin W → ℝ => fun i => divisorAreaMoment (d i) a) := by
  let T := derivativeAreaMatrix d
  have hdet : IsUnit T.det := isUnit_iff_ne_zero.mpr (derivative_area_matrix_nondegenerate hd)
  exact Matrix.mulVec_injective_iff_isUnit.mpr (T.isUnit_iff_isUnit_det.mpr hdet)

theorem group_derivative_moment_by_order (t : Finset ℂ) (W j : ℕ)
    (hlo : ∀ z ∈ t, 0 < hadamardOrder z) (hhi : ∀ z ∈ t, hadamardOrder z≤W) :
    divisorAreaMoment j (fun k => (divisorOrderCounts t W k:ℝ)) =
      ∑ z ∈ t, (hadamardOrder z:ℝ)^(2/((j+1:ℕ):ℝ)) := by
  classical
  have hc (k : Fin W) : (divisorOrderCounts t W k:ℝ) =
      ∑ z ∈ t, if hadamardOrder z=k.val+1 then (1:ℝ) else 0 := by
    rw [←Finset.sum_filter]
    simp [divisorOrderCounts]
  simp only [divisorAreaMoment,hc,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have hp := hlo z hz
  have hm := hhi z hz
  let k : Fin W := ⟨hadamardOrder z-1,by omega⟩
  have he : k.val+1=hadamardOrder z := by dsimp [k]; omega
  rw [Finset.sum_eq_single k]
  · simp only [he,if_true,mul_one,orderAreaWeight]
  · intro b _ hne
    have hne' : hadamardOrder z≠b.val+1 := fun h => hne (Fin.ext (by omega))
    rw [if_neg hne',mul_zero]
  · simp

/-- The winding bounds all component counts. Each observable area
converges to the corresponding moment of this same integer histogram. -/
theorem xi_disk_bounded_order_counts (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    let W := (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat
    ∃ t : Finset ℂ, (∀ z, z∈t ↔ ‖z-c‖<R ∧ xi z=0) ∧
      (∀ k : Fin W, divisorOrderCounts t W k≤W) ∧
      ∀ j, Tendsto (xiDerivativeDiskArea j c R) atTop
        (𝓝 (divisorAreaMoment j (fun k => (divisorOrderCounts t W k:ℝ)))) := by
  classical
  obtain ⟨t,ht,hw,ha⟩ := xi_disk_fractional_moments c hR hb
  let W := ∑ z ∈ t, hadamardOrder z
  have hW : (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat=W := by
    rw [hw,←Nat.cast_sum,Int.toNat_natCast]
  dsimp only
  rw [hW]
  have hp (z : ℂ) (hz : z∈t) : 0<hadamardOrder z := Nat.pos_of_ne_zero
    (fun h => (hadamardOrder_zero_iff z).mp h ((ht z).mp hz).2)
  have hm (z : ℂ) (hz : z∈t) : hadamardOrder z≤W :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hz
  have hcard : t.card≤W := by
    calc t.card = ∑ _z ∈ t, 1 := by simp
         _ ≤ W := Finset.sum_le_sum hp
  exact ⟨t,ht,fun k => (Finset.card_filter_le ..).trans hcard,
    fun j => by rw [group_derivative_moment_by_order t W j hp hm]; exact ha j⟩

/-- Multiplying the measured areas by the inverse calibration matrix
recovers each integer count in the limit. -/
theorem any_derivative_schedule_recovers_counts (c : ℂ) {R : ℝ} (hR : 0<R)
    (hb : ∀ z, ‖z-c‖=R → xi z≠0) :
    let W := (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat
    ∃ t : Finset ℂ, (∀ z, z∈t ↔ ‖z-c‖<R ∧ xi z=0) ∧
      ∀ (d : Fin W → ℕ), StrictMono d → ∀ k : Fin W,
        Tendsto (fun u : ℝ => ((derivativeAreaMatrix d)⁻¹ *ᵥ (fun i => xiDerivativeDiskArea (d i) c R u)) k)
          atTop (𝓝 (divisorOrderCounts t W k:ℝ)) := by
  obtain ⟨t,ht,_,ha⟩ := xi_disk_bounded_order_counts c hR hb
  refine ⟨t,ht,?_⟩
  intro d hd k
  let W := (windingNumber (fun θ => xi (c+↑R*exp (I*↑θ))) 0 (2*Real.pi)).toNat
  let T := derivativeAreaMatrix d
  let v : Fin W → ℝ := fun i => (divisorOrderCounts t W i:ℝ)
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin W)) fun i _ => (ha (d i)).const_mul (T⁻¹ k i)
  have hinv : T⁻¹*T=1 := T.nonsing_inv_mul (isUnit_iff_ne_zero.mpr (derivative_area_matrix_nondegenerate hd))
  change Tendsto _ _ (𝓝 ((T⁻¹ *ᵥ (T *ᵥ v)) k)) at h
  rwa [Matrix.mulVec_mulVec,hinv,Matrix.one_mulVec] at h

#print axioms derivative_area_matrix_nondegenerate
#print axioms any_derivative_schedule_recovers_counts
end GaloisForLFunctions.ExceptionalLayerTheory
