import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Ground-state representation: pointwise identities and the finite jump form

For reals `ω_x, ω_y, u_x, u_y` the difference `ω_x u_x − ω_y u_y` and the sum `ω_x u_x + ω_y u_y`
split exactly into a "ground-state transformed" square and a term whose second factor is
antisymmetric under the exchange `x ↔ y`. Summed against a symmetric kernel the antisymmetric term
becomes twice the quadratic pairing of `u² ω` with the generator applied to `ω`. This is the
ground-state representation of a jump form, and it gives the easy half of the
Allegretto–Piepenbrink theorem: a positive supersolution of `L_K ω ≥ ρ ω` forces
`E_K(v) ≥ Σ ρ_i v_i²` for every `v`.

The finite objects are `jumpEnergy K v = ½ Σ_{i,j} K_{ij} (v_i − v_j)²`,
`generator K ω i = Σ_j K_{ij} (ω_i − ω_j)` and `groundKernel K ω i j = K_{ij} ω_i ω_j`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- Difference identity: `(ω_x u_x − ω_y u_y)² = ω_x ω_y (u_x − u_y)² + (ω_x − ω_y)(ω_x u_x² − ω_y u_y²)`. -/
theorem groundState_difference_identity (ωx ωy ux uy : ℝ) :
    (ωx * ux - ωy * uy) ^ 2 =
      ωx * ωy * (ux - uy) ^ 2 + (ωx - ωy) * (ωx * ux ^ 2 - ωy * uy ^ 2) := by
  ring

/-- Sum identity in Neumann form: the remainder is the square of the sum `u_x + u_y`, and the
potential term is the same antisymmetric product as in the difference identity. -/
theorem groundState_sum_identity (ωx ωy ux uy : ℝ) :
    (ωx * ux + ωy * uy) ^ 2 =
      ωx * ωy * (ux + uy) ^ 2 + (ωx - ωy) * (ωx * ux ^ 2 - ωy * uy ^ 2) := by
  ring

/-- Sum identity in Dirichlet form: the remainder is a negative difference square and the potential
term carries `ω_x + ω_y`, the generator of the odd extension. -/
theorem groundState_sum_identity_twoSided (ωx ωy ux uy : ℝ) :
    (ωx * ux + ωy * uy) ^ 2 =
      -(ωx * ωy * (ux - uy) ^ 2) + (ωx + ωy) * (ωx * ux ^ 2 + ωy * uy ^ 2) := by
  ring

section Finite

variable {ι : Type*} [Fintype ι]

/-- The jump energy `½ Σ_{i,j} K_{ij} (v_i − v_j)²` of a finite kernel; every unordered pair is
counted once when `K` is symmetric. -/
def jumpEnergy (K : ι → ι → ℝ) (v : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, K i j * (v i - v j) ^ 2

/-- The generator `(L_K ω)_i = Σ_j K_{ij} (ω_i − ω_j)`. -/
def generator (K : ι → ι → ℝ) (ω : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, K i j * (ω i - ω j)

/-- The ground-state transformed kernel `K_{ij} ω_i ω_j`. -/
def groundKernel (K : ι → ι → ℝ) (ω : ι → ℝ) (i j : ι) : ℝ :=
  K i j * ω i * ω j

theorem jumpEnergy_nonneg {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j) (v : ι → ℝ) :
    0 ≤ jumpEnergy K v := by
  unfold jumpEnergy
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  exact mul_nonneg (hK i j) (sq_nonneg _)

omit [Fintype ι] in
theorem groundKernel_nonneg {K : ι → ι → ℝ} (hK : ∀ i j, 0 ≤ K i j) {ω : ι → ℝ}
    (hω : ∀ i, 0 ≤ ω i) (i j : ι) : 0 ≤ groundKernel K ω i j := by
  unfold groundKernel
  exact mul_nonneg (mul_nonneg (hK i j) (hω i)) (hω j)

omit [Fintype ι] in
theorem groundKernel_symm {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i) (ω : ι → ℝ) (i j : ι) :
    groundKernel K ω i j = groundKernel K ω j i := by
  unfold groundKernel
  rw [hK i j]
  ring

/-- The antisymmetric product summed against a symmetric kernel is twice the generator pairing. -/
theorem potential_double_sum {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i) (ω u : ι → ℝ) :
    ∑ i, ∑ j, K i j * ((ω i - ω j) * (ω i * u i ^ 2 - ω j * u j ^ 2)) =
      2 * ∑ i, u i ^ 2 * ω i * generator K ω i := by
  have hsplit : ∀ i j, K i j * ((ω i - ω j) * (ω i * u i ^ 2 - ω j * u j ^ 2)) =
      K i j * (ω i - ω j) * ω i * u i ^ 2 + K j i * (ω j - ω i) * ω j * u j ^ 2 := by
    intro i j
    rw [hK j i]
    ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hcomm : ∑ i, ∑ j, K j i * (ω j - ω i) * ω j * u j ^ 2 =
      ∑ i, ∑ j, K i j * (ω i - ω j) * ω i * u i ^ 2 := Finset.sum_comm
  rw [hcomm, ← two_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold generator
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Finite ground-state representation.** For a symmetric kernel,
`E_K(ω u) = E_{K ω⊗ω}(u) + Σ_i u_i² ω_i (L_K ω)_i`. -/
theorem jumpEnergy_groundState {K : ι → ι → ℝ} (hK : ∀ i j, K i j = K j i) (ω u : ι → ℝ) :
    jumpEnergy K (fun i => ω i * u i) =
      jumpEnergy (groundKernel K ω) u + ∑ i, u i ^ 2 * ω i * generator K ω i := by
  unfold jumpEnergy
  have hpt : ∀ i j, K i j * (ω i * u i - ω j * u j) ^ 2 =
      groundKernel K ω i j * (u i - u j) ^ 2 +
        K i j * ((ω i - ω j) * (ω i * u i ^ 2 - ω j * u j ^ 2)) := by
    intro i j
    unfold groundKernel
    ring
  simp_rw [hpt, Finset.sum_add_distrib]
  rw [potential_double_sum hK ω u]
  ring

/-- **Allegretto–Piepenbrink, easy direction (finite).** A strictly positive supersolution
`ρ_i ω_i ≤ (L_K ω)_i` of a symmetric nonnegative kernel forces `Σ ρ_i v_i² ≤ E_K(v)` for all `v`. -/
theorem sum_potential_le_jumpEnergy_of_supersolution {K : ι → ι → ℝ}
    (hK : ∀ i j, K i j = K j i) (hK0 : ∀ i j, 0 ≤ K i j) {ω : ι → ℝ} (hω : ∀ i, 0 < ω i)
    {ρ : ι → ℝ} (hsuper : ∀ i, ρ i * ω i ≤ generator K ω i) (v : ι → ℝ) :
    ∑ i, ρ i * v i ^ 2 ≤ jumpEnergy K v := by
  have key := jumpEnergy_groundState hK ω (fun i => v i / ω i)
  have hfun : (fun i => ω i * (v i / ω i)) = v := by
    funext i
    field_simp [(hω i).ne']
  rw [hfun] at key
  rw [key]
  have h1 : 0 ≤ jumpEnergy (groundKernel K ω) (fun i => v i / ω i) :=
    jumpEnergy_nonneg (groundKernel_nonneg hK0 fun i => (hω i).le) _
  have h2 : ∑ i, ρ i * v i ^ 2 ≤ ∑ i, (v i / ω i) ^ 2 * ω i * generator K ω i := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hw := hω i
    have hmul := mul_le_mul_of_nonneg_left (hsuper i)
      (by positivity : (0 : ℝ) ≤ (v i / ω i) ^ 2 * ω i)
    calc ρ i * v i ^ 2 = (v i / ω i) ^ 2 * ω i * (ρ i * ω i) := by
          field_simp
      _ ≤ (v i / ω i) ^ 2 * ω i * generator K ω i := hmul
  linarith

end Finite

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
