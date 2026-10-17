import GaloisForLFunctions.BiScaleUncertainty.SharedOriginMultiCosetLeverage

/-!
# Support of paired coset spheres

Every block on one sign shares a Bessel sphere with every block on the other sign.
The support function combines the two sums of block norms in Euclidean norm.
This is sharper than treating all signed blocks independently, and is attained
in precisely the finite paired-sphere relaxation.
-/

set_option autoImplicit false
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
variable {ι κ : Type*}

/-- The support scale for two families with all opposite-family sphere constraints. -/
def pairedSphereScale (M : Finset ι) (s : ι → Finset κ)
    (w : Bool → ι → κ → ℝ) (W : ℝ) : ℝ :=
  Real.sqrt (W ^ 2 + blockWeightNorm M s (w false) ^ 2 +
    blockWeightNorm M s (w true) ^ 2)

/-- Pairwise sphere compatibility improves the sum of the two sign norms to
their Euclidean norm, while charging the common origin only once. -/
theorem paired_sphere_weighted_sum_le (M : Finset ι) (hM : M.Nonempty)
    (s : ι → Finset κ) (w u : Bool → ι → κ → ℝ) (W u₀ R : ℝ) (hR : 0 ≤ R)
    (hsph : ∀ p ∈ M, ∀ q ∈ M,
      u₀ ^ 2 + (∑ k ∈ s p, u false p k ^ 2) +
        (∑ k ∈ s q, u true q k ^ 2) ≤ R ^ 2) :
    W * u₀ + (∑ p ∈ M, ∑ k ∈ s p, w false p k * u false p k) +
      (∑ q ∈ M, ∑ k ∈ s q, w true q k * u true q k) ≤
        pairedSphereScale M s w W * R := by
  let Q (σ : Bool) := M.sup' hM (fun m => ∑ k ∈ s m, u σ m k ^ 2)
  let r (σ : Bool) := Real.sqrt (Q σ)
  have hQ (σ : Bool) : 0 ≤ Q σ := by
    obtain ⟨m, hm⟩ := hM
    exact (Finset.sum_nonneg fun k _ => sq_nonneg (u σ m k)).trans
      (Finset.le_sup' (fun m => ∑ k ∈ s m, u σ m k ^ 2) hm)
  have hr (σ : Bool) : r σ ^ 2 = Q σ := Real.sq_sqrt (hQ σ)
  obtain ⟨p, hp, heqp⟩ := Finset.exists_mem_eq_sup' hM
    (fun m => ∑ k ∈ s m, u false m k ^ 2)
  obtain ⟨q, hq, heqq⟩ := Finset.exists_mem_eq_sup' hM
    (fun m => ∑ k ∈ s m, u true m k ^ 2)
  have hpair : u₀ ^ 2 + r false ^ 2 + r true ^ 2 ≤ R ^ 2 := by
    rw [hr false, hr true]
    simpa only [Q, heqp, heqq] using hsph p hp q hq
  have hblock (σ : Bool) (m : ι) (hm : m ∈ M) :
      (∑ k ∈ s m, w σ m k * u σ m k) ≤
        Real.sqrt (∑ k ∈ s m, w σ m k ^ 2) * r σ := by
    have h := sphere_weighted_sum_le_sqrt_mul (s m) 0 (w σ m) (u σ m) 0
      (r σ) (Real.sqrt_nonneg _) (by
        simp only [zero_pow (by decide : 2 ≠ 0), zero_add]
        rw [hr]
        exact Finset.le_sup' (fun p => ∑ k ∈ s p, u σ p k ^ 2) hm)
    simpa only [zero_mul, zero_add, zero_pow (by decide : 2 ≠ 0)] using h
  have hsum (σ : Bool) :
      (∑ m ∈ M, ∑ k ∈ s m, w σ m k * u σ m k) ≤
        blockWeightNorm M s (w σ) * r σ := by
    simpa only [blockWeightNorm, Finset.sum_mul] using Finset.sum_le_sum (hblock σ)
  have hfinal := sphere_weighted_sum_le_sqrt_mul (Finset.univ : Finset Bool) W
    (fun σ => blockWeightNorm M s (w σ)) r u₀ R hR (by
      simpa only [Fintype.sum_bool, add_assoc, add_comm, add_left_comm] using hpair)
  have hscale : Real.sqrt (W ^ 2 +
      (blockWeightNorm M s (w true) ^ 2 + blockWeightNorm M s (w false) ^ 2)) =
        pairedSphereScale M s w W := by
    unfold pairedSphereScale
    congr 1
    ring
  simp only [Fintype.sum_bool, hscale] at hfinal
  linarith [hsum false, hsum true]

/-- The corresponding deficit bound on the paired-sphere domain. -/
theorem paired_sphere_leverage_bound (M : Finset ι) (hM : M.Nonempty)
    (s : ι → Finset κ) (w u : Bool → ι → κ → ℝ) (W u₀ R : ℝ) (hR : 0 ≤ R)
    (hsph : ∀ p ∈ M, ∀ q ∈ M,
      u₀ ^ 2 + (∑ k ∈ s p, u false p k ^ 2) +
        (∑ k ∈ s q, u true q k ^ 2) ≤ R ^ 2) :
    (W + (∑ p ∈ M, ∑ k ∈ s p, w false p k) +
      (∑ q ∈ M, ∑ k ∈ s q, w true q k) - pairedSphereScale M s w W) * R ≤
        W * (R - u₀) +
          (∑ p ∈ M, ∑ k ∈ s p, w false p k * (R - u false p k)) +
          (∑ q ∈ M, ∑ k ∈ s q, w true q k * (R - u true q k)) := by
  have h := paired_sphere_weighted_sum_le M hM s w u W u₀ R hR hsph
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  nlinarith

/-- Product coupling never enlarges the independent-sign support scale. -/
theorem pairedSphereScale_le_independent (M : Finset ι) (s : ι → Finset κ)
    (w : Bool → ι → κ → ℝ) (W : ℝ) :
    pairedSphereScale M s w W ≤
      Real.sqrt (W ^ 2 + (blockWeightNorm M s (w false) + blockWeightNorm M s (w true)) ^ 2) := by
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg (blockWeightNorm_nonneg M s (w false))
    (blockWeightNorm_nonneg M s (w true))]

/-- The exact support reduction is the cross-sign norm product, rationalized. -/
theorem pairedSphereScale_gain (M : Finset ι) (s : ι → Finset κ)
    (w : Bool → ι → κ → ℝ) {W : ℝ} (hW : 0 < W) :
    Real.sqrt (W ^ 2 + (blockWeightNorm M s (w false) + blockWeightNorm M s (w true)) ^ 2) -
      pairedSphereScale M s w W =
        2 * blockWeightNorm M s (w false) * blockWeightNorm M s (w true) /
          (Real.sqrt (W ^ 2 + (blockWeightNorm M s (w false) + blockWeightNorm M s (w true)) ^ 2) +
            pairedSphereScale M s w W) := by
  let A := blockWeightNorm M s (w false)
  let B := blockWeightNorm M s (w true)
  let P := Real.sqrt (W ^ 2 + (A + B) ^ 2)
  let Q := pairedSphereScale M s w W
  have hP : P ^ 2 = W ^ 2 + (A + B) ^ 2 := Real.sq_sqrt (by positivity)
  have hQ : Q ^ 2 = W ^ 2 + A ^ 2 + B ^ 2 := Real.sq_sqrt (by positivity)
  have hQpos : 0 < Q := Real.sqrt_pos.2 (by positivity)
  have hsum : P + Q ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hQpos)
  change P - Q = 2 * A * B / (P + Q)
  apply (eq_div_iff hsum).2
  nlinarith

/-- The paired-sphere support is attained by parallel blocks on each sign.
This asserts finite-vector sharpness, without asserting correlation realizability. -/
theorem paired_sphere_support_attained (M : Finset ι) (s : ι → Finset κ)
    (w : Bool → ι → κ → ℝ) {W : ℝ} (hW : 0 < W) (R : ℝ) :
    ∃ (u₀ : ℝ) (u : Bool → ι → κ → ℝ),
      (∀ p ∈ M, ∀ q ∈ M,
        u₀ ^ 2 + (∑ k ∈ s p, u false p k ^ 2) +
          (∑ k ∈ s q, u true q k ^ 2) ≤ R ^ 2) ∧
      W * u₀ + (∑ p ∈ M, ∑ k ∈ s p, w false p k * u false p k) +
        (∑ q ∈ M, ∑ k ∈ s q, w true q k * u true q k) =
          pairedSphereScale M s w W * R := by
  let A (σ : Bool) := blockWeightNorm M s (w σ)
  let D := pairedSphereScale M s w W
  have hDsq : D ^ 2 = W ^ 2 + A false ^ 2 + A true ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hD : D ≠ 0 := by
    intro hz
    rw [hz] at hDsq
    nlinarith [sq_nonneg (A false), sq_nonneg (A true)]
  let a := R * W / D
  let b (σ : Bool) := R * A σ / D
  have hab : a ^ 2 + b false ^ 2 + b true ^ 2 = R ^ 2 := by
    dsimp [a, b]
    calc
      _ = R ^ 2 * (W ^ 2 + A false ^ 2 + A true ^ 2) / D ^ 2 := by ring
      _ = R ^ 2 := by rw [← hDsq]; field_simp
  let v (σ : Bool) (m : ι) (k : κ) :=
    w σ m k / Real.sqrt (∑ j ∈ s m, w σ m j ^ 2)
  have hv (σ : Bool) (m : ι) : (∑ k ∈ s m, v σ m k ^ 2) ≤ 1 := by
    let q := Real.sqrt (∑ j ∈ s m, w σ m j ^ 2)
    have hq : q ^ 2 = ∑ j ∈ s m, w σ m j ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (w σ m j))
    change (∑ k ∈ s m, (w σ m k / q) ^ 2) ≤ 1
    simp_rw [div_pow, ← Finset.sum_div]
    rw [← hq]
    by_cases hz : q = 0 <;> simp [hz]
  have hwv (σ : Bool) (m : ι) :
      (∑ k ∈ s m, w σ m k * v σ m k) = Real.sqrt (∑ j ∈ s m, w σ m j ^ 2) := by
    let q := Real.sqrt (∑ j ∈ s m, w σ m j ^ 2)
    have hq : q ^ 2 = ∑ j ∈ s m, w σ m j ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (w σ m j))
    change (∑ k ∈ s m, w σ m k * (w σ m k / q)) = q
    simp_rw [show ∀ k, w σ m k * (w σ m k / q) = w σ m k ^ 2 / q by intro k; ring]
    rw [← Finset.sum_div, ← hq]
    by_cases hz : q = 0
    · simp [hz]
    · field_simp
  refine ⟨a, (fun σ m k => b σ * v σ m k), ?_, ?_⟩
  · intro p _ q _
    have hp := mul_le_mul_of_nonneg_left (hv false p) (sq_nonneg (b false))
    have hq := mul_le_mul_of_nonneg_left (hv true q) (sq_nonneg (b true))
    simp_rw [mul_pow, ← Finset.mul_sum]
    nlinarith
  · have hsum (σ : Bool) :
        (∑ m ∈ M, ∑ k ∈ s m, w σ m k * (b σ * v σ m k)) = b σ * A σ := by
      calc
        _ = ∑ m ∈ M, b σ * ∑ k ∈ s m, w σ m k * v σ m k := by
          apply Finset.sum_congr rfl
          intro m _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = b σ * A σ := by simp only [hwv, A, blockWeightNorm, Finset.mul_sum]
    rw [hsum false, hsum true]
    change W * a + b false * A false + b true * A true = D * R
    dsimp [a, b]
    calc
      _ = R * (W ^ 2 + A false ^ 2 + A true ^ 2) / D := by ring
      _ = D * R := by rw [← hDsq]; field_simp

end
end GaloisForLFunctions.BiScaleUncertainty
