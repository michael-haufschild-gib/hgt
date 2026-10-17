import GaloisForLFunctions.BiScaleUncertainty.PairedCollarCutoffStability
import GaloisForLFunctions.BiScaleUncertainty.CollarEndpointTailMass

/-!
# Quantitative floor-square-root normalization

Replacing the real square root of the source cutoff by its integer floor
changes the inverse square root by at most an inverse physical cutoff.
This controls the delayed paired hierarchy at its natural fourth-root scale.
-/

set_option autoImplicit false
open Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

theorem floorSqrtCutoff_bounds {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℝ) ≤ (Nat.sqrt (n + 2) : ℝ) ∧
    (Nat.sqrt (n + 2) : ℝ) ≤ Real.sqrt ((n + 2 : ℕ) : ℝ) ∧
    Real.sqrt ((n + 2 : ℕ) : ℝ) < (Nat.sqrt (n + 2) : ℝ) + 1 ∧
    Real.sqrt ((n + 2 : ℕ) : ℝ) ≤ 2 * (Nat.sqrt (n + 2) : ℝ) := by
  let s : ℝ := (Nat.sqrt (n + 2) : ℝ)
  let X : ℝ := ((n + 2 : ℕ) : ℝ)
  have hsNat : 2 ≤ Nat.sqrt (n + 2) := Nat.le_sqrt'.2 (by omega)
  have hs : 2 ≤ s := by
    dsimp [s]
    exact_mod_cast hsNat
  have hlo : s ^ 2 ≤ X := by
    dsimp [s, X]
    exact_mod_cast Nat.sqrt_le' (n + 2)
  have hhi : X < (s + 1) ^ 2 := by
    dsimp [s, X]
    exact_mod_cast Nat.lt_succ_sqrt' (n + 2)
  refine ⟨hs, Real.le_sqrt_of_sq_le hlo, ?_, ?_⟩
  · exact (Real.sqrt_lt' (by linarith : 0 < s + 1)).2 hhi
  · apply Real.sqrt_le_iff.mpr
    exact ⟨by linarith, by nlinarith [sq_nonneg (s - 1)]⟩

/-- A mesh error of at most one gives an inverse-cutoff inverse-root error. -/
theorem inverse_sqrt_mesh_error {s x : ℝ} (hs : 1 ≤ s) (hsx : s ≤ x) (hgap : x - s ≤ 1) :
    0 ≤ 1 / Real.sqrt s - 1 / Real.sqrt x ∧
      1 / Real.sqrt s - 1 / Real.sqrt x ≤ 1 / s := by
  let u := Real.sqrt s
  let v := Real.sqrt x
  have hsp : 0 < s := by linarith
  have hxp : 0 < x := hsp.trans_le hsx
  have hu : 0 < u := Real.sqrt_pos.mpr hsp
  have hv : 0 < v := Real.sqrt_pos.mpr hxp
  have huu : u ^ 2 = s := Real.sq_sqrt hsp.le
  have hvv : v ^ 2 = x := Real.sq_sqrt hxp.le
  have hu1 : 1 ≤ u := Real.le_sqrt_of_sq_le (by simpa only [one_pow] using hs)
  have huv : u ≤ v := Real.sqrt_le_sqrt hsx
  have hv1 : 1 ≤ v := hu1.trans huv
  have hd : 0 ≤ v - u := sub_nonneg.mpr huv
  have hlinear : u * (v - u) ≤ 1 := by
    nlinarith [mul_nonneg hv.le hd]
  have hid : 1 / u - 1 / v = (v - u) / (u * v) := by
    field_simp [hu.ne', hv.ne']
  change 0 ≤ 1 / u - 1 / v ∧ 1 / u - 1 / v ≤ 1 / s
  rw [hid]
  constructor
  · exact div_nonneg hd (mul_pos hu hv).le
  · apply (div_le_div_iff₀ (mul_pos hu hv) hsp).mpr
    have hm := mul_le_mul_of_nonneg_left (hlinear.trans hv1) hu.le
    have hp : (v - u) * s ≤ u * v := by
      calc
        _ = (v - u) * u ^ 2 := by rw [huu]
        _ = u * (u * (v - u)) := by ring
        _ ≤ _ := hm
    simpa only [one_mul] using hp

theorem inverse_sqrt_floor_cutoff_error {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ 1 / Real.sqrt (Nat.sqrt (n + 2) : ℝ) -
      1 / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) ∧
    1 / Real.sqrt (Nat.sqrt (n + 2) : ℝ) -
      1 / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ)) ≤ 1 / (Nat.sqrt (n + 2) : ℝ) := by
  have h := floorSqrtCutoff_bounds hn
  exact inverse_sqrt_mesh_error (by linarith [h.1]) h.2.1 (by linarith [h.2.2.1])

theorem floorSqrtCutoff_inverse_le {n : ℕ} (hn : 2 ≤ n) :
    1 / (Nat.sqrt (n + 2) : ℝ) ≤ 2 / Real.sqrt ((n + 2 : ℕ) : ℝ) := by
  have h := floorSqrtCutoff_bounds hn
  apply (div_le_div_iff₀ (by linarith [h.1]) (by positivity)).mpr
  simpa only [one_mul] using h.2.2.2

theorem productAdmittedCutoff_ge_six {n : ℕ} (hn : 62 ≤ n) :
    6 ≤ productAdmittedCutoff n := by
  have h : 8 ≤ Nat.sqrt (n + 2) := Nat.le_sqrt'.2 (by omega)
  unfold productAdmittedCutoff
  omega

theorem tendsto_inverse_fourthRoot_collarCutoff :
    Tendsto (fun n : ℕ => 1 / Real.sqrt (Real.sqrt ((n + 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp tendsto_inverse_sqrt_collarCutoff
  change Tendsto (fun n : ℕ => Real.sqrt (1 / Real.sqrt ((n + 2 : ℕ) : ℝ)))
    atTop (𝓝 (Real.sqrt 0)) at h
  simpa only [Real.sqrt_div zero_le_one, Real.sqrt_one, Real.sqrt_zero] using h

end
end GaloisForLFunctions.BiScaleUncertainty
