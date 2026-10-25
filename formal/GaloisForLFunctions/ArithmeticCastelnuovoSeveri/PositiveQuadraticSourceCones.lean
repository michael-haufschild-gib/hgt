import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ExactArithmeticSourceEffectivity
import GaloisForLFunctions.HTGeometry.NonnegFormRadical

/-!
# Positive quadratic reserves give additive source cones

A positive quadratic source reserve has the Cauchy bound needed for closure under
addition and nonnegative scaling. This is a property of the effective set; it does
not assert Riemann–Roch for the original intersection pairing.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface
variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

private theorem quadratic_product_sum_bound (a b c d u v w : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hv : 0 ≤ v) (huab : u ≤ 2 * a * b) (hvcd : v ≤ 2 * c * d)
    (hw : w ^ 2 ≤ u * v) : u + 2 * w + v ≤ 2 * (a + c) * (b + d) := by
  have hprod := mul_le_mul huab hvcd hv (by positivity : 0 ≤ 2 * a * b)
  have hcross : 0 ≤ a * d + b * c := add_nonneg (mul_nonneg ha hd) (mul_nonneg hb hc)
  have hcrossSq : 4 * a * b * c * d ≤ (a * d + b * c) ^ 2 := by
    nlinarith only [sq_nonneg (a * d - b * c)]
  have hwcross : w ≤ a * d + b * c := by
    nlinarith only [hw, hprod, hcrossSq, hcross]
  nlinarith only [huab, hvcd, hwcross]

/-- A positive quadratic reserve gives an additive effective source set. -/
theorem sourceCone_quadratic_add_closed
    (Q : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) (hsymm : ∀ x y, Q x y = Q y x)
    (hnn : ∀ x, 0 ≤ Q x x) :
    ∀ x ∈ S.sourceCone (fun z => Q z z),
      ∀ y ∈ S.sourceCone (fun z => Q z z),
        x + y ∈ S.sourceCone (fun z => Q z z) := by
  intro x hx y hy
  rw [S.mem_sourceCone_iff] at hx hy ⊢
  refine ⟨?_, ?_, ?_⟩
  · simpa only [map_add, LinearMap.add_apply] using add_nonneg hx.1 hy.1
  · simpa only [map_add, LinearMap.add_apply] using add_nonneg hx.2.1 hy.2.1
  · rw [S.polar_self] at hx hy
    have h := quadratic_product_sum_bound
      (S.pair x S.H) (S.pair x S.V) (S.pair y S.H) (S.pair y S.V)
      (Q x x) (Q y y) (Q x y) hx.1 hx.2.1 hy.1 hy.2.1
      (hnn y) hx.2.2 hy.2.2 (GaloisForLFunctions.HTGeometry.bilinForm_sq_le Q hsymm hnn x y)
    simp only [S.polar_self, map_add, LinearMap.add_apply, hsymm y x]
    nlinarith only [h]

/-- A quadratic source cone contains zero. -/
theorem zero_mem_sourceCone_quadratic (Q : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) :
    (0 : C) ∈ S.sourceCone (fun z => Q z z) := by
  rw [S.mem_sourceCone_iff]
  simp only [S.polar_self, map_zero, LinearMap.zero_apply, mul_zero, le_refl, and_self]

/-- Quadratic source effectivity is preserved by every nonnegative scalar. -/
theorem smul_mem_sourceCone_quadratic
    (Q : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) {a : ℝ} (ha : 0 ≤ a) {x : C}
    (hx : x ∈ S.sourceCone (fun z => Q z z)) :
    a • x ∈ S.sourceCone (fun z => Q z z) := by
  rw [S.mem_sourceCone_iff] at hx ⊢
  refine ⟨?_, ?_, ?_⟩
  · simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul] using mul_nonneg ha hx.1
  · simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul] using mul_nonneg ha hx.2.1
  · rw [S.polar_self] at hx
    have h := mul_le_mul_of_nonneg_left hx.2.2 (sq_nonneg a)
    simp only [S.polar_self, map_smul, LinearMap.smul_apply, smul_eq_mul]
    nlinarith only [h]

/-- Every positive quadratic source reserve defines a convex effective set. -/
theorem sourceCone_quadratic_convex
    (Q : C →ₗ[ℝ] C →ₗ[ℝ] ℝ) (hsymm : ∀ x y, Q x y = Q y x)
    (hnn : ∀ x, 0 ≤ Q x x) : Convex ℝ (S.sourceCone (fun z => Q z z)) := by
  intro x hx y hy a b ha hb _
  exact S.sourceCone_quadratic_add_closed Q hsymm hnn (a • x)
    (S.smul_mem_sourceCone_quadratic Q ha hx) (b • y)
    (S.smul_mem_sourceCone_quadratic Q hb hy)

/-- Every finite fibre-invariant source threshold containing the fibre quadrant is generating. -/
theorem sourceCone_generating {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x)
    (hzero : Φ 0 ≤ 0) (x : C) :
    ∃ y ∈ S.sourceCone Φ, ∃ z ∈ S.sourceCone Φ, x = y - z := by
  let M := |S.pair x S.H| + |S.pair x S.V| + |Φ x| + 1
  have hM : 0 ≤ M := by
    dsimp only [M]
    linarith only [abs_nonneg (S.pair x S.H), abs_nonneg (S.pair x S.V), abs_nonneg (Φ x)]
  let z := M • S.H + M • S.V
  have hzH : S.pair z S.H = M := by
    simp only [z, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, S.pair_H_H, S.pair_V_H, mul_zero, mul_one, zero_add]
  have hzV : S.pair z S.V = M := by
    simp only [z, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, S.pair_H_V, S.pair_V_V, mul_zero, mul_one, add_zero]
  have hzΦ : Φ z = Φ 0 := by
    simpa only [zero_add] using hfib 0 M M
  have hz : z ∈ S.sourceCone Φ := by
    rw [S.mem_sourceCone_iff, S.polar_self, hzH, hzV, hzΦ]
    exact ⟨hM, hM, hzero.trans (by positivity)⟩
  have hxΦ : Φ (x + z) = Φ x := by
    simpa only [z, add_assoc] using hfib x M M
  have hxH : S.pair (x + z) S.H = S.pair x S.H + M := by
    simp only [map_add, LinearMap.add_apply, hzH]
  have hxV : S.pair (x + z) S.V = S.pair x S.V + M := by
    simp only [map_add, LinearMap.add_apply, hzV]
  have ha : 1 ≤ S.pair x S.H + M := by
    dsimp only [M]
    linarith only [neg_le_abs (S.pair x S.H), abs_nonneg (S.pair x S.V), abs_nonneg (Φ x)]
  have hb : |Φ x| + 1 ≤ S.pair x S.V + M := by
    dsimp only [M]
    linarith only [abs_nonneg (S.pair x S.H), neg_le_abs (S.pair x S.V)]
  have hab := mul_le_mul ha hb (by positivity : 0 ≤ |Φ x| + 1)
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) ha)
  have hy : x + z ∈ S.sourceCone Φ := by
    rw [S.mem_sourceCone_iff, S.polar_self, hxΦ, hxH, hxV]
    refine ⟨by linarith only [ha], by linarith only [hb, abs_nonneg (Φ x)], ?_⟩
    nlinarith only [hab, le_abs_self (Φ x), abs_nonneg (Φ x)]
  exact ⟨x + z, hy, z, hz, by abel⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface
