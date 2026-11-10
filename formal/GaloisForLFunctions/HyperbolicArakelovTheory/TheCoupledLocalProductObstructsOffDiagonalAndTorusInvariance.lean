import GaloisForLFunctions.HyperbolicArakelovTheory.TheFullAdelicDegreeConfiguration
import GaloisForLFunctions.HyperbolicArakelovTheory.TheCriticalAdelicOrbitRequiresGlobalRenormalization
import Mathlib.NumberTheory.Pell

/-!
# The coupled local critical product obstructs off-diagonal contacts and torus cutoffs

Multiplying the archimedean critical profile `archProfile (h3Dist x₁ y₁)` on `ℍ³` by the restricted
product of the normalized critical Bruhat–Tits tree Green kernels
`G^{T_p}_{1/2}(d_p) / G^{T_p}_{1/2}(0) = p^{-d_p / 2}` across all finite places gives an
`AdelicGroup`-invariant two-point function `adelicCriticalProduct` on `GlobalSpace = ℍ³ × V`.

This file proves both its positive global symmetries and the four obstructions preventing its
rational torus orbit sum from realizing Weil's bilinear form on the degree points:

1. **`AdelicGroup`-invariance and adelic degree-shift homogeneity (`adelicCriticalProduct_smul`,
   `adelicDegreeShift_smul_one`, `adelicDegreeShift_comm_torus`,
   `adelicCriticalProduct_torus_diag_eq`).** The adelic shift `δ_n = (diag(√n, 1/√n), (diag(n, 1))_p)`
   maps `x_1` to `x_n` and commutes in `AdelicGroup` with the entire rational torus `T(ℚ)`, making
   the diagonal torus profile at `x_n` identical to that at `x_1` (and equal on `Primitive` to
   `CoupledOrbit.term 2`).
2. **Closed rational formula and erasure of prime contacts (`adelicCriticalProduct_torus_pos_rat`,
   `adelicCriticalProduct_degree_eq`, `adelicCriticalProduct_one_degree_eq`).** At the identity
   element `q = 1`, the product formula collapses `∏_p G^{T_p}_{1/2}(d_p)/G^{T_p}_{1/2}(0)` to
   `gcd(m, n) / √(m n)`, so `adelicCriticalProduct x_m x_n = gcd(m, n) max(m, n) / |n² - m²|`
   (at `m = 1 < n`: `n / (n² - 1)`), erasing the prime contact weights `Λ(n/m)` completely.
3. **Interior square-ratio collisions, Pell non-decay, and universal off-diagonal divergence
   (`offDiag_torus_arch_collision`, `adelicCriticalProduct_pell_gt_half_inv`,
   `adelicCriticalProduct_one_two_pell_eq`, `not_summable_adelicCriticalProduct_torus_noncolliding`).**
   Distinct degree classes `[x_m] ≠ [x_{m k²}]` (`k ≥ 2`) collide in `ℍ³` at `q = 1/k` with strictly
   positive finite factor `k⁻²`; for non-square `m * n`, Pell units give infinitely many torus
   elements along which `adelicCriticalProduct x_m (γ_q • x_n) > 1 / (2 m)` fails to decay to zero
   (exceeding `1` for `(1, 2)`); and for *every* `(m, n)`, the non-colliding torus orbit series
   diverges.
4. **Height cutoff non-invariance (`weilHeight_mul_prime_of_one_lt`,
   `weilHeight_ball_mul_prime_ssubset`).** Scaling `q > 1` by a prime `p` multiplies `weilHeight q`
   by `1` if `p ∣ q.den` and by `p` otherwise, strictly shrinking every cutoff ball `N ≥ 5`.
-/

set_option autoImplicit false
noncomputable section

open Matrix Set Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.HyperbolicArakelovTheory.CoupledProductObstruction

open FullAdelic SurfaceOfSpecZ

local instance (p : {p : ℕ // p.Prime}) : Fact p.1.Prime := ⟨p.2⟩

/-! ## 1. Normalized critical tree Green factor on `PGL₂(ℚ_p)/K_p` -/

/-- Maximum entry norm of a `2 × 2` matrix over `ℚ_p`. -/
def matrixMaxNorm (p : {p : ℕ // p.Prime}) (A : Matrix (Fin 2) (Fin 2) ℚ_[p.1]) : ℝ :=
  max (max ‖A 0 0‖ ‖A 0 1‖) (max ‖A 1 0‖ ‖A 1 1‖)

theorem entry_le_matrixMaxNorm (p : {p : ℕ // p.Prime}) (A : Matrix (Fin 2) (Fin 2) ℚ_[p.1])
    (i j : Fin 2) : ‖A i j‖ ≤ matrixMaxNorm p A := by
  fin_cases i <;> fin_cases j <;> simp [matrixMaxNorm]

theorem matrixMaxNorm_le_iff (p : {p : ℕ // p.Prime}) (A : Matrix (Fin 2) (Fin 2) ℚ_[p.1])
    (c : ℝ) : matrixMaxNorm p A ≤ c ↔ ∀ i j : Fin 2, ‖A i j‖ ≤ c := by
  constructor
  · intro h i j
    exact (entry_le_matrixMaxNorm p A i j).trans h
  · intro h
    exact max_le (max_le (h 0 0) (h 0 1)) (max_le (h 1 0) (h 1 1))

theorem matrixMaxNorm_pos (p : {p : ℕ // p.Prime}) (g : LocalGL p) :
    0 < matrixMaxNorm p g.val := by
  have hnn : 0 ≤ matrixMaxNorm p g.val :=
    (norm_nonneg (g 0 0)).trans (entry_le_matrixMaxNorm p g.val 0 0)
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · exfalso
    have hall := (matrixMaxNorm_le_iff p g.val 0).mp h0.symm.le
    have hz : ∀ i j : Fin 2, g.val i j = 0 := fun i j =>
      norm_eq_zero.mp (le_antisymm (hall i j) (norm_nonneg _))
    have hdet := g.det_ne_zero
    rw [Matrix.det_fin_two, hz 0 0, hz 0 1, hz 1 0, hz 1 1] at hdet
    simp at hdet
  · exact hpos

theorem matrixMaxNorm_smul (p : {p : ℕ // p.Prime}) (u : ℚ_[p.1])
    (A : Matrix (Fin 2) (Fin 2) ℚ_[p.1]) :
    matrixMaxNorm p (u • A) = ‖u‖ * matrixMaxNorm p A := by
  by_cases hu : u = 0
  · subst hu
    simp [matrixMaxNorm]
  · have hle : ∀ (v : ℚ_[p.1]) (B : Matrix (Fin 2) (Fin 2) ℚ_[p.1]),
        matrixMaxNorm p (v • B) ≤ ‖v‖ * matrixMaxNorm p B := by
      intro v B
      refine (matrixMaxNorm_le_iff p _ _).mpr fun i j => ?_
      rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (entry_le_matrixMaxNorm p B i j) (norm_nonneg v)
    apply le_antisymm (hle u A)
    have hinv := hle u⁻¹ (u • A)
    rw [inv_smul_smul₀ hu, norm_inv] at hinv
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hmul := mul_le_mul_of_nonneg_left hinv hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at hmul

theorem matrixMaxNorm_mul_scalar (p : {p : ℕ // p.Prime}) (A : Matrix (Fin 2) (Fin 2) ℚ_[p.1])
    (u : ℚ_[p.1]) :
    matrixMaxNorm p (A * Matrix.scalar (Fin 2) u) = ‖u‖ * matrixMaxNorm p A := by
  have heq : A * Matrix.scalar (Fin 2) u = u • A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  rw [heq, matrixMaxNorm_smul]

theorem matrixMaxNorm_mul_integral_right (p : {p : ℕ // p.Prime})
    (A : Matrix (Fin 2) (Fin 2) ℚ_[p.1]) (k : GL (Fin 2) ℤ_[p.1]) :
    matrixMaxNorm p (A * (integralMap p k).val) = matrixMaxNorm p A := by
  have hle : ∀ (B : Matrix (Fin 2) (Fin 2) ℚ_[p.1]) (h : GL (Fin 2) ℤ_[p.1]),
      matrixMaxNorm p (B * (integralMap p h).val) ≤ matrixMaxNorm p B := by
    intro B h
    refine (matrixMaxNorm_le_iff p _ _).mpr fun i j => ?_
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (h 0 j).2).trans
        (entry_le_matrixMaxNorm p B i 0)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (h 1 j).2).trans
        (entry_le_matrixMaxNorm p B i 1)
  apply le_antisymm (hle A k)
  have hinv := hle (A * (integralMap p k).val) k⁻¹
  have hcancel : A * (integralMap p k).val * (integralMap p k⁻¹).val = A := by
    rw [Matrix.mul_assoc, ← GeneralLinearGroup.coe_mul, ← map_mul, mul_inv_cancel,
      map_one, GeneralLinearGroup.coe_one, Matrix.mul_one]
  rwa [hcancel] at hinv

theorem matrixMaxNorm_mul_integral_left (p : {p : ℕ // p.Prime})
    (k : GL (Fin 2) ℤ_[p.1]) (A : Matrix (Fin 2) (Fin 2) ℚ_[p.1]) :
    matrixMaxNorm p ((integralMap p k).val * A) = matrixMaxNorm p A := by
  have hle : ∀ (h : GL (Fin 2) ℤ_[p.1]) (B : Matrix (Fin 2) (Fin 2) ℚ_[p.1]),
      matrixMaxNorm p ((integralMap p h).val * B) ≤ matrixMaxNorm p B := by
    intro h B
    refine (matrixMaxNorm_le_iff p _ _).mpr fun i j => ?_
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (h i 0).2).trans
        (entry_le_matrixMaxNorm p B 0 j)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (h i 1).2).trans
        (entry_le_matrixMaxNorm p B 1 j)
  apply le_antisymm (hle k A)
  have hinv := hle k⁻¹ ((integralMap p k).val * A)
  have hcancel : (integralMap p k⁻¹).val * ((integralMap p k).val * A) = A := by
    rw [← Matrix.mul_assoc, ← GeneralLinearGroup.coe_mul, ← map_mul, inv_mul_cancel,
      map_one, GeneralLinearGroup.coe_one, Matrix.one_mul]
  rwa [hcancel] at hinv

theorem matrixMaxNorm_adjugate (p : {p : ℕ // p.Prime}) (A : Matrix (Fin 2) (Fin 2) ℚ_[p.1]) :
    matrixMaxNorm p A.adjugate = matrixMaxNorm p A := by
  apply le_antisymm
  · refine (matrixMaxNorm_le_iff p _ _).mpr fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.adjugate_fin_two, entry_le_matrixMaxNorm]
  · refine (matrixMaxNorm_le_iff p _ _).mpr fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa [Matrix.adjugate_fin_two] using entry_le_matrixMaxNorm p A.adjugate 1 1
    · simpa [Matrix.adjugate_fin_two] using entry_le_matrixMaxNorm p A.adjugate 0 1
    · simpa [Matrix.adjugate_fin_two] using entry_le_matrixMaxNorm p A.adjugate 1 0
    · simpa [Matrix.adjugate_fin_two] using entry_le_matrixMaxNorm p A.adjugate 0 0

/-- Scale-invariant bi-`GL₂(ℤ_p)`-invariant local Green factor on `GL₂(ℚ_p)`. -/
def glFactor (p : {p : ℕ // p.Prime}) (g : LocalGL p) : ℝ :=
  Real.sqrt ‖g.val.det‖ / matrixMaxNorm p g.val

theorem glFactor_pos (p : {p : ℕ // p.Prime}) (g : LocalGL p) : 0 < glFactor p g :=
  div_pos (Real.sqrt_pos.mpr (norm_pos_iff.mpr g.det_ne_zero)) (matrixMaxNorm_pos p g)

theorem glFactor_one (p : {p : ℕ // p.Prime}) : glFactor p 1 = 1 := by
  unfold glFactor
  have hm : matrixMaxNorm p (1 : Matrix (Fin 2) (Fin 2) ℚ_[p.1]) = 1 := by
    simp [matrixMaxNorm]
  rw [GeneralLinearGroup.coe_one, Matrix.det_one, norm_one, Real.sqrt_one, hm, div_one]

theorem glFactor_mul_scalar (p : {p : ℕ // p.Prime}) (g : LocalGL p) (u : (ℚ_[p.1])ˣ) :
    glFactor p (g * GeneralLinearGroup.scalar (Fin 2) u) = glFactor p g := by
  have hu : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero
  have hdet : ‖(g * GeneralLinearGroup.scalar (Fin 2) u).val.det‖ =
      ‖g.val.det‖ * ‖u.val‖ ^ 2 := by
    rw [GeneralLinearGroup.coe_mul, Matrix.det_mul, GeneralLinearGroup.coe_scalar,
      Matrix.det_fin_two, norm_mul]
    congr 1
    simp [Matrix.scalar_apply, sq, norm_mul]
  unfold glFactor
  rw [hdet, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq hu.le, GeneralLinearGroup.coe_mul,
    GeneralLinearGroup.coe_scalar, matrixMaxNorm_mul_scalar]
  field_simp [hu.ne', (matrixMaxNorm_pos p g).ne']

theorem glFactor_inv (p : {p : ℕ // p.Prime}) (g : LocalGL p) :
    glFactor p g⁻¹ = glFactor p g := by
  have hd_pos : 0 < ‖g.val.det‖ := norm_pos_iff.mpr g.det_ne_zero
  have hadj : g.val.det • g⁻¹.val = g.val.adjugate := by
    calc g.val.det • g⁻¹.val
        = g⁻¹.val * (g.val.det • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p.1])) := by
          rw [Matrix.mul_smul, Matrix.mul_one]
      _ = g⁻¹.val * (g.val * g.val.adjugate) := by rw [Matrix.mul_adjugate]
      _ = (g⁻¹.val * g.val) * g.val.adjugate := by rw [Matrix.mul_assoc]
      _ = g.val.adjugate := by
          rw [← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one,
            Matrix.one_mul]
  have hm : ‖g.val.det‖ * matrixMaxNorm p g⁻¹.val = matrixMaxNorm p g.val := by
    rw [← matrixMaxNorm_smul, hadj, matrixMaxNorm_adjugate]
  have hdet_inv : ‖g⁻¹.val.det‖ = ‖g.val.det‖⁻¹ := by
    have hmul : g⁻¹.val.det * g.val.det = 1 := by
      rw [← Matrix.det_mul, ← GeneralLinearGroup.coe_mul, inv_mul_cancel,
        GeneralLinearGroup.coe_one, Matrix.det_one]
    have hnm := congrArg norm hmul
    rw [norm_mul, norm_one] at hnm
    exact eq_inv_of_mul_eq_one_left hnm
  unfold glFactor
  rw [hdet_inv, Real.sqrt_inv, ← hm]
  have hsd : 0 < Real.sqrt ‖g.val.det‖ := Real.sqrt_pos.mpr hd_pos
  have hsq : Real.sqrt ‖g.val.det‖ ^ 2 = ‖g.val.det‖ := Real.sq_sqrt hd_pos.le
  field_simp [hsd.ne', hd_pos.ne', (matrixMaxNorm_pos p g⁻¹).ne']
  rw [hsq]

theorem glFactor_integral_right (p : {p : ℕ // p.Prime}) (g : LocalGL p)
    (k : GL (Fin 2) ℤ_[p.1]) : glFactor p (g * integralMap p k) = glFactor p g := by
  unfold glFactor
  rw [GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul, integralMap_det_norm, mul_one,
    matrixMaxNorm_mul_integral_right]

theorem glFactor_integral_left (p : {p : ℕ // p.Prime}) (k : GL (Fin 2) ℤ_[p.1])
    (g : LocalGL p) : glFactor p (integralMap p k * g) = glFactor p g := by
  unfold glFactor
  rw [GeneralLinearGroup.coe_mul, Matrix.det_mul, norm_mul, integralMap_det_norm, one_mul,
    matrixMaxNorm_mul_integral_left]

/-- Descent of `glFactor` to `PGL₂(ℚ_p)`. -/
def pglFactor (p : {p : ℕ // p.Prime}) : LocalPGL p → ℝ :=
  Quotient.lift (glFactor p) (by
    intro g₁ g₂ h
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp (Quotient.sound h)
    rw [← hu, glFactor_mul_scalar])

@[simp] theorem pglFactor_mk (p : {p : ℕ // p.Prime}) (g : LocalGL p) :
    pglFactor p (ProjGenLinGroup.mk g) = glFactor p g := rfl

theorem pglFactor_one (p : {p : ℕ // p.Prime}) : pglFactor p 1 = 1 :=
  glFactor_one p

theorem pglFactor_inv (p : {p : ℕ // p.Prime}) (x : LocalPGL p) :
    pglFactor p x⁻¹ = pglFactor p x := by
  induction x using Quotient.inductionOn with
  | h g => exact glFactor_inv p g

theorem pglFactor_mul_mem_right (p : {p : ℕ // p.Prime}) (x : LocalPGL p) {k : LocalPGL p}
    (hk : k ∈ integralPGL p) : pglFactor p (x * k) = pglFactor p x := by
  obtain ⟨u, rfl⟩ := hk
  induction x using Quotient.inductionOn with
  | h g => exact glFactor_integral_right p g u

theorem pglFactor_mul_mem_left (p : {p : ℕ // p.Prime}) {k : LocalPGL p}
    (hk : k ∈ integralPGL p) (x : LocalPGL p) : pglFactor p (k * x) = pglFactor p x := by
  obtain ⟨u, rfl⟩ := hk
  induction x using Quotient.inductionOn with
  | h g => exact glFactor_integral_left p u g

/-- The `PGL₂(ℚ_p)`-invariant normalized critical tree Green kernel `p^{-d_p(v, w)/2}` on
`PGL₂(ℚ_p)/K_p`. -/
def localFactor (p : {p : ℕ // p.Prime}) (v w : LocalVertex p) : ℝ :=
  Quotient.lift₂ (fun x y : LocalPGL p => pglFactor p (x⁻¹ * y)) (by
    intro x₁ y₁ x₂ y₂ hx hy
    have hkx : x₁⁻¹ * x₂ ∈ integralPGL p := QuotientGroup.leftRel_apply.mp hx
    have hky : y₁⁻¹ * y₂ ∈ integralPGL p := QuotientGroup.leftRel_apply.mp hy
    have hkxi : x₂⁻¹ * x₁ ∈ integralPGL p := by
      simpa only [_root_.mul_inv_rev, inv_inv] using (integralPGL p).inv_mem hkx
    have hrel : x₂⁻¹ * y₂ = (x₂⁻¹ * x₁) * (x₁⁻¹ * y₁) * (y₁⁻¹ * y₂) := by group
    rw [hrel, pglFactor_mul_mem_right p _ hky, pglFactor_mul_mem_left p hkxi]) v w

@[simp] theorem localFactor_mk (p : {p : ℕ // p.Prime}) (x y : LocalPGL p) :
    localFactor p (QuotientGroup.mk x) (QuotientGroup.mk y) = pglFactor p (x⁻¹ * y) := rfl

theorem localFactor_smul (p : {p : ℕ // p.Prime}) (g : LocalPGL p) (v w : LocalVertex p) :
    localFactor p (g • v) (g • w) = localFactor p v w := by
  induction v using Quotient.inductionOn with
  | h x =>
    induction w using Quotient.inductionOn with
    | h y =>
      change pglFactor p ((g * x)⁻¹ * (g * y)) = pglFactor p (x⁻¹ * y)
      congr 1
      group

theorem localFactor_self (p : {p : ℕ // p.Prime}) (v : LocalVertex p) :
    localFactor p v v = 1 := by
  induction v using Quotient.inductionOn with
  | h x =>
    change pglFactor p (x⁻¹ * x) = 1
    rw [inv_mul_cancel, pglFactor_one]

theorem localFactor_comm (p : {p : ℕ // p.Prime}) (v w : LocalVertex p) :
    localFactor p v w = localFactor p w v := by
  induction v using Quotient.inductionOn with
  | h x =>
    induction w using Quotient.inductionOn with
    | h y =>
      change pglFactor p (x⁻¹ * y) = pglFactor p (y⁻¹ * x)
      rw [← pglFactor_inv p (y⁻¹ * x)]
      congr 1
      group

theorem localFactor_pos (p : {p : ℕ // p.Prime}) (v w : LocalVertex p) :
    0 < localFactor p v w := by
  induction v using Quotient.inductionOn with
  | h x =>
    induction w using Quotient.inductionOn with
    | h y =>
      have hz : x⁻¹ * y = ProjGenLinGroup.mk (Quotient.out (x⁻¹ * y)) :=
        (Quotient.out_eq _).symm
      change 0 < pglFactor p (x⁻¹ * y)
      rw [hz, pglFactor_mk]
      exact glFactor_pos p _

theorem hasFiniteMulSupport_localFactor (u v : FiniteVertices) :
    Function.HasFiniteMulSupport (fun p => localFactor p (u.1 p) (v.1 p)) := by
  refine (u.2.union v.2).subset fun p hp => ?_
  by_contra hnot
  have hbase : u.1 p = baseVertex p ∧ v.1 p = baseVertex p := by
    simpa only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] using hnot
  apply hp
  change localFactor p (u.1 p) (v.1 p) = 1
  rw [hbase.1, hbase.2, localFactor_self]

/-! ## 2. Global `AdelicGroup`-invariant critical product and adelic degree shift -/

/-- Restricted product of all normalized finite-place critical tree Green kernels. -/
def finiteGreenProduct (u v : FiniteVertices) : ℝ :=
  ∏ᶠ p : {p : ℕ // p.Prime}, localFactor p (u.1 p) (v.1 p)

theorem finiteGreenProduct_smul (a : FiniteAdelicGroup) (u v : FiniteVertices) :
    finiteGreenProduct (a • u) (a • v) = finiteGreenProduct u v := by
  unfold finiteGreenProduct
  congr 1
  funext p
  exact localFactor_smul p (a p) (u.1 p) (v.1 p)

theorem h3Dist_h3Act (g : SL2C) (p q : H3) :
    h3Dist (h3Act g p) (h3Act g q) = h3Dist p q := by
  rw [h3Dist, h3Dist, h3Cosh_h3Act]

/-- Global `AdelicGroup`-invariant critical Green product on `GlobalSpace = ℍ³ × V`. -/
def adelicCriticalProduct (x y : GlobalSpace) : ℝ :=
  archProfile (h3Dist x.1 y.1) * finiteGreenProduct x.2 y.2

theorem adelicCriticalProduct_smul (g : AdelicGroup) (x y : GlobalSpace) :
    adelicCriticalProduct (g • x) (g • y) = adelicCriticalProduct x y := by
  unfold adelicCriticalProduct
  change archProfile (h3Dist (h3Act g.1 x.1) (h3Act g.1 y.1)) *
    finiteGreenProduct (g.2 • x.2) (g.2 • y.2) = _
  rw [h3Dist_h3Act, finiteGreenProduct_smul]

/-- The rational split torus inside `conjugateArithmeticGroup`. -/
def torusElem (q : ℚ) (hq : q ≠ 0) : conjugateArithmeticGroup :=
  ⟨conjugateEmbedding (OppositeAdelic.diagonal q hq), ⟨OppositeAdelic.diagonal q hq, rfl⟩⟩

private theorem weyl_conj_diagonal (q : ℚ) (hq : q ≠ 0) :
    OppositeAdelic.weyl⁻¹ * OppositeAdelic.diagonal q hq * OppositeAdelic.weyl =
      OppositeAdelic.diagonal q⁻¹ (inv_ne_zero hq) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [OppositeAdelic.weyl, OppositeAdelic.diagonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- Adelic split-torus element `δ_n = (diag(√n, 1/√n), (diag(n, 1))_p) ∈ AdelicGroup` translating
`x_1` to `x_n` and commuting with `T(ℚ)`. -/
def adelicDegreeShift (n : ℕ+) : AdelicGroup :=
  (diagSL2 ((Real.sqrt (n : ℝ) : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast n.pos)).ne'),
    ⟨fun p => ProjGenLinGroup.mk (localGLMap p (upperDegree n)), by
      rw [Filter.eventually_cofinite]
      refine (principalVertex_finite_support (upperDegree n)).subset fun p hp => ?_
      intro heq
      apply hp
      have hh := QuotientGroup.eq.mp heq
      rw [mul_one, Subgroup.inv_mem_iff] at hh
      exact hh⟩)

theorem adelicDegreeShift_smul_one (n : ℕ+) :
    adelicDegreeShift n • originalDegreePoint 1 = originalDegreePoint n := by
  apply Prod.ext
  · change h3Act (adelicDegreeShift n).1
      (degPoint ((1 : ℕ) : ℝ) (by exact_mod_cast (1 : ℕ+).pos)) =
      degPoint ((n : ℕ) : ℝ) (by exact_mod_cast n.pos)
    dsimp only [adelicDegreeShift]
    rw [h3Act_diag]
    apply degPoint_eq
    have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast n.pos.le
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hn0,
      Nat.cast_one, mul_one]
  · apply Subtype.ext
    funext p
    change QuotientGroup.mk (ProjGenLinGroup.mk (localGLMap p (upperDegree n)) *
      ProjGenLinGroup.mk (localGLMap p (upperDegree 1))) =
      QuotientGroup.mk (ProjGenLinGroup.mk (localGLMap p (upperDegree n)))
    rw [← map_mul, ← map_mul]
    have hu1 : upperDegree n * upperDegree 1 = upperDegree n := by
      apply GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [upperDegree, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hu1]

/-- `adelicDegreeShift n` commutes with every element of the rational torus `T(ℚ)` inside
`AdelicGroup`. -/
theorem adelicDegreeShift_comm_torus (n : ℕ+) (q : ℚ) (hq : q ≠ 0) :
    adelicDegreeShift n * (torusElem q hq : AdelicGroup) =
      (torusElem q hq : AdelicGroup) * adelicDegreeShift n := by
  apply Prod.ext
  · change (adelicDegreeShift n).1 * (conjugateEmbedding (OppositeAdelic.diagonal q hq)).1 =
      (conjugateEmbedding (OppositeAdelic.diagonal q hq)).1 * (adelicDegreeShift n).1
    rw [conjugateEmbedding_arch]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adelicDegreeShift, diagSL2, OppositeAdelic.archMap,
        OppositeAdelic.diagonal, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  · apply RestrictedProduct.ext
    intro p
    change ProjGenLinGroup.mk (localGLMap p (upperDegree n)) *
      (conjugateEmbedding (OppositeAdelic.diagonal q hq)).2 p =
      (conjugateEmbedding (OppositeAdelic.diagonal q hq)).2 p *
      ProjGenLinGroup.mk (localGLMap p (upperDegree n))
    rw [conjugateEmbedding_finite, weyl_conj_diagonal, localProj_toGL, ← map_mul, ← map_mul,
      ← map_mul, ← map_mul]
    congr 2
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [upperDegree, SpecialLinearGroup.toGL, OppositeAdelic.diagonal,
        Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- For every `n : ℕ+` and `q ∈ ℚˣ`, the torus-displaced diagonal critical product at `x_n`
is identical to that at `x_1`. -/
theorem adelicCriticalProduct_torus_diag_eq (n : ℕ+) (q : ℚ) (hq : q ≠ 0) :
    adelicCriticalProduct (originalDegreePoint n)
        ((torusElem q hq : AdelicGroup) • originalDegreePoint n) =
      adelicCriticalProduct (originalDegreePoint 1)
        ((torusElem q hq : AdelicGroup) • originalDegreePoint 1) := by
  rw [← adelicDegreeShift_smul_one n, ← mul_smul, ← adelicDegreeShift_comm_torus n q hq,
    mul_smul, adelicCriticalProduct_smul]

/-! ## 3. Exact rational evaluation on degree points and torus displacements -/

/-- Diagonal rational matrix `diag(u, v) ∈ GL₂(ℚ)` for `u, v : ℕ+`. -/
def diagGL (u v : ℕ+) : RationalGL :=
  ⟨!![((u : ℕ) : ℚ), 0; 0, ((v : ℕ) : ℚ)],
    !![(((u : ℕ) : ℚ))⁻¹, 0; 0, (((v : ℕ) : ℚ))⁻¹],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, u.ne_zero, v.ne_zero],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, u.ne_zero, v.ne_zero]⟩

private theorem padic_norm_pnat (p : {p : ℕ // p.Prime}) (n : ℕ+) :
    ‖((n : ℕ) : ℚ_[p.1])‖ = (((p.1 ^ (n : ℕ).factorization p.1 : ℕ) : ℝ))⁻¹ := by
  set k := (n : ℕ).factorization p.1
  set m := (n : ℕ) / p.1 ^ k
  have hdvd : p.1 ^ k ∣ (n : ℕ) := Nat.ordProj_dvd (n : ℕ) p.1
  have hndvd : ¬ p.1 ∣ m := Nat.not_dvd_ordCompl p.2 n.ne_zero
  have hnm : (n : ℕ) = p.1 ^ k * m := (Nat.mul_div_cancel' hdvd).symm
  have hm_norm : ‖(m : ℚ_[p.1])‖ = 1 := by
    change ‖((m : ℚ) : ℚ_[p.1])‖ = 1
    rw [Padic.eq_padicNorm, (padicNorm.nat_eq_one_iff (p := p.1) m).mpr hndvd]
    exact Rat.cast_one
  conv_lhs => rw [hnm]
  push_cast
  rw [norm_mul, Padic.norm_p_pow, hm_norm, mul_one, _root_.zpow_neg, zpow_natCast]

private theorem max_padic_norm_pnat (p : {p : ℕ // p.Prime}) (u v : ℕ+) :
    max ‖((u : ℕ) : ℚ_[p.1])‖ ‖((v : ℕ) : ℚ_[p.1])‖ =
      ‖((Nat.gcd (u : ℕ) v : ℕ) : ℚ_[p.1])‖ := by
  let g : ℕ+ := ⟨Nat.gcd (u : ℕ) v, Nat.gcd_pos_of_pos_left _ u.pos⟩
  change _ = ‖((g : ℕ) : ℚ_[p.1])‖
  rw [padic_norm_pnat, padic_norm_pnat, padic_norm_pnat]
  have hfg : (g : ℕ).factorization p.1 =
      min ((u : ℕ).factorization p.1) ((v : ℕ).factorization p.1) := by
    simp only [g, PNat.mk_coe, Nat.factorization_gcd u.ne_zero v.ne_zero, Finsupp.inf_apply]
  rw [hfg]
  rcases le_total ((u : ℕ).factorization p.1) ((v : ℕ).factorization p.1) with hle | hle
  · rw [min_eq_left hle, max_eq_left]
    exact inv_anti₀ (by exact_mod_cast pow_pos p.2.pos _)
      (by exact_mod_cast Nat.pow_le_pow_right p.2.pos hle)
  · rw [min_eq_right hle, max_eq_right]
    exact inv_anti₀ (by exact_mod_cast pow_pos p.2.pos _)
      (by exact_mod_cast Nat.pow_le_pow_right p.2.pos hle)

theorem glFactor_diagGL (p : {p : ℕ // p.Prime}) (u v : ℕ+) :
    glFactor p (localGLMap p (diagGL u v)) =
      Real.sqrt ‖((u : ℕ) : ℚ_[p.1])‖ * Real.sqrt ‖((v : ℕ) : ℚ_[p.1])‖ /
        ‖((Nat.gcd (u : ℕ) v : ℕ) : ℚ_[p.1])‖ := by
  unfold glFactor
  have hdet : (localGLMap p (diagGL u v)).val.det =
      ((u : ℕ) : ℚ_[p.1]) * ((v : ℕ) : ℚ_[p.1]) := by
    rw [Matrix.det_fin_two]
    simp [localGLMap_apply, diagGL]
  have hm : matrixMaxNorm p (localGLMap p (diagGL u v)).val =
      ‖((Nat.gcd (u : ℕ) v : ℕ) : ℚ_[p.1])‖ := by
    unfold matrixMaxNorm
    simp only [localGLMap_apply, diagGL, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Rat.cast_zero, norm_zero, Rat.cast_natCast,
      max_eq_left (norm_nonneg _), max_eq_right (norm_nonneg _)]
    exact max_padic_norm_pnat p u v
  rw [hdet, norm_mul, Real.sqrt_mul (norm_nonneg _), hm]

private theorem coe_scalar_apply {R : Type*} [CommRing R] (u : Rˣ) (i j : Fin 2) :
    (GeneralLinearGroup.scalar (Fin 2) u : Matrix (Fin 2) (Fin 2) R) i j =
      if i = j then (u : R) else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

private theorem localGLMap_scalar (p : {p : ℕ // p.Prime}) (u : ℚˣ) :
    localGLMap p (GeneralLinearGroup.scalar (Fin 2) u) =
      GeneralLinearGroup.scalar (Fin 2)
        (Units.mk0 ((u : ℚ) : ℚ_[p.1]) (by exact_mod_cast u.ne_zero)) := by
  apply Units.ext
  ext i j
  change ((localGLMap p (GeneralLinearGroup.scalar (Fin 2) u) :
      Matrix (Fin 2) (Fin 2) ℚ_[p.1]) i j) =
    (GeneralLinearGroup.scalar (Fin 2)
      (Units.mk0 ((u : ℚ) : ℚ_[p.1]) (by exact_mod_cast u.ne_zero)) :
      Matrix (Fin 2) (Fin 2) ℚ_[p.1]) i j
  rw [localGLMap_apply, coe_scalar_apply, coe_scalar_apply]
  split_ifs <;> simp

/-- On degree vertices, `localFactor p` equals the normalized critical tree Green function
`G^{T_p}_{1/2}(|v_p(m) - v_p(n)|) / G^{T_p}_{1/2}(0)`. -/
theorem localFactor_upperDegree_eq_treeGreen (p : {p : ℕ // p.Prime}) (m n : ℕ+) :
    localFactor p (principalVertex (upperDegree m) p) (principalVertex (upperDegree n) p) =
      treeGreen p.1 (1 / 2) (((m : ℕ).factorization p.1 : ℤ) - (n : ℕ).factorization p.1).natAbs /
        treeGreen p.1 (1 / 2) 0 := by
  obtain ⟨uQ, huQ⟩ : ∃ u : ℚˣ, (u : ℚ) = ((m : ℕ) : ℚ) :=
    ⟨Units.mk0 ((m : ℕ) : ℚ) (by exact_mod_cast m.ne_zero), rfl⟩
  have hrelQ : (upperDegree m)⁻¹ * upperDegree n *
      GeneralLinearGroup.scalar (Fin 2) uQ = diagGL n m := by
    rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simp [upperDegree, diagGL, Matrix.mul_apply, Fin.sum_univ_two]
      rw [huQ, mul_comm]
    · simp [upperDegree, diagGL, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [upperDegree, diagGL, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [upperDegree, diagGL, Matrix.mul_apply, Fin.sum_univ_two]
      exact huQ
  let uP : (ℚ_[p.1])ˣ := Units.mk0 ((uQ : ℚ) : ℚ_[p.1]) (by exact_mod_cast uQ.ne_zero)
  have hrel : (localGLMap p (upperDegree m))⁻¹ * localGLMap p (upperDegree n) *
      GeneralLinearGroup.scalar (Fin 2) uP =
      localGLMap p (diagGL n m) := by
    have hmap := congrArg (localGLMap p) hrelQ
    rw [map_mul, map_mul, map_inv, localGLMap_scalar] at hmap
    exact hmap
  change pglFactor p ((ProjGenLinGroup.mk (localGLMap p (upperDegree m)))⁻¹ *
    ProjGenLinGroup.mk (localGLMap p (upperDegree n))) = _
  rw [← map_inv, ← map_mul, pglFactor_mk, ← glFactor_mul_scalar p _ uP, hrel, glFactor_diagGL]
  let g : ℕ+ := ⟨Nat.gcd (n : ℕ) m, Nat.gcd_pos_of_pos_left _ n.pos⟩
  change _ / ‖((g : ℕ) : ℚ_[p.1])‖ = _
  rw [padic_norm_pnat, padic_norm_pnat, padic_norm_pnat]
  have hp0 : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
  have hcoeff : (p.1 : ℝ) ^ (1 / 2 : ℝ) / ((p.1 : ℝ) ^ (2 * (1 / 2) : ℝ) - 1) ≠ 0 := by
    norm_num only [mul_one_div_cancel, Real.rpow_one]
    exact div_ne_zero (Real.rpow_pos_of_pos hp0 _).ne' (by linarith only [hp1])
  unfold treeGreen
  rw [pow_zero, mul_one, mul_div_cancel_left₀ _ hcoeff]
  set a := (m : ℕ).factorization p.1
  set b := (n : ℕ).factorization p.1
  have hfg : (g : ℕ).factorization p.1 = min b a := by
    simp only [g, PNat.mk_coe, Nat.factorization_gcd n.ne_zero m.ne_zero, Finsupp.inf_apply]
    rfl
  rw [hfg]
  have hrw : ∀ k : ℕ, (((p.1 ^ k : ℕ) : ℝ))⁻¹ = (p.1 : ℝ) ^ (-(k : ℝ)) := fun k => by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_neg hp0.le]
  have hsqrt : ∀ k : ℕ, Real.sqrt (((p.1 ^ k : ℕ) : ℝ)⁻¹) = (p.1 : ℝ) ^ (-(k : ℝ) / 2) :=
    fun k => by
      rw [hrw k, Real.sqrt_eq_rpow, ← Real.rpow_mul hp0.le]
      congr 1
      ring
  rw [hsqrt b, hsqrt a, hrw (min b a), ← Real.rpow_add hp0, div_eq_mul_inv,
    ← Real.rpow_neg hp0.le, ← Real.rpow_add hp0, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  congr 1
  have habs : a + b - 2 * min b a = ((a : ℤ) - b).natAbs := by omega
  have hle : 2 * min b a ≤ a + b := by omega
  have hexp : (a : ℝ) + b - 2 * ((min b a : ℕ) : ℝ) = (((a : ℤ) - b).natAbs : ℝ) := by
    have hnat : ((a + b - 2 * min b a : ℕ) : ℝ) = (((a : ℤ) - b).natAbs : ℝ) := by
      exact_mod_cast habs
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hnat
    exact hnat
  linarith [hexp]

private theorem prod_sqrt_nonneg {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) :
    (∏ x ∈ s, Real.sqrt (f x)) = Real.sqrt (∏ x ∈ s, f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)),
      ← Real.sqrt_mul (hf a (Finset.mem_insert_self a s))]

private theorem prod_prime_pow_factorization_of_dvd {N : ℕ} (hN : N ≠ 0) (k : ℕ+)
    (hdvd : (k : ℕ) ∣ N) :
    (∏ q ∈ N.primeFactors, ((q ^ (k : ℕ).factorization q : ℕ) : ℝ)) = (k : ℝ) := by
  have hsub : (k : ℕ).primeFactors ⊆ N.primeFactors := Nat.primeFactors_mono hdvd hN
  have hprod : (∏ q ∈ N.primeFactors, q ^ (k : ℕ).factorization q) = (k : ℕ) := by
    rw [← Finset.prod_subset hsub]
    · exact (Nat.prod_primeFactors_pow_factorization k.ne_zero).symm
    · intro q _ hq
      have hnd : ¬ q ∣ (k : ℕ) := fun hd =>
        hq (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors ‹_›, hd, k.ne_zero⟩)
      rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero]
  exact_mod_cast hprod

/-- Restricted product of `glFactor p (diag(u, v))` over all primes equals `gcd(u, v) / √(u v)`. -/
theorem finprod_glFactor_diagGL (u v : ℕ+) :
    (∏ᶠ p : {p : ℕ // p.Prime}, glFactor p (localGLMap p (diagGL u v))) =
      (Nat.gcd (u : ℕ) v : ℝ) / Real.sqrt ((u : ℝ) * v) := by
  let N : ℕ := (u : ℕ) * v
  have hN : N ≠ 0 := mul_ne_zero u.ne_zero v.ne_zero
  let g : ℕ+ := ⟨Nat.gcd (u : ℕ) v, Nat.gcd_pos_of_pos_left _ u.pos⟩
  let emb : {q : ℕ // q ∈ N.primeFactors} ↪ {p : ℕ // p.Prime} :=
    ⟨fun q => ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩,
      fun q₁ q₂ h => Subtype.ext (Subtype.mk.inj h)⟩
  let S : Finset {p : ℕ // p.Prime} := N.primeFactors.attach.map emb
  have hsupp : Function.mulSupport (fun p => glFactor p (localGLMap p (diagGL u v))) ⊆ ↑S := by
    intro p hp
    by_contra hnot
    have hpN : p.1 ∉ N.primeFactors := by
      intro hm
      exact hnot (Finset.mem_coe.mpr (Finset.mem_map.mpr
        ⟨⟨p.1, hm⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩))
    have hndN : ¬ p.1 ∣ N := fun hd => hpN (Nat.mem_primeFactors.mpr ⟨p.2, hd, hN⟩)
    have hnd_u : ¬ p.1 ∣ (u : ℕ) := fun hd => hndN (dvd_mul_of_dvd_left hd _)
    have hnd_v : ¬ p.1 ∣ (v : ℕ) := fun hd => hndN (dvd_mul_of_dvd_right hd _)
    have hnd_g : ¬ p.1 ∣ (g : ℕ) := fun hd => hnd_u (hd.trans (Nat.gcd_dvd_left _ _))
    apply hp
    change glFactor p (localGLMap p (diagGL u v)) = 1
    rw [glFactor_diagGL]
    change Real.sqrt ‖((u : ℕ) : ℚ_[p.1])‖ * Real.sqrt ‖((v : ℕ) : ℚ_[p.1])‖ /
      ‖((g : ℕ) : ℚ_[p.1])‖ = 1
    rw [padic_norm_pnat, padic_norm_pnat, padic_norm_pnat,
      Nat.factorization_eq_zero_of_not_dvd hnd_u, Nat.factorization_eq_zero_of_not_dvd hnd_v,
      Nat.factorization_eq_zero_of_not_dvd hnd_g]
    simp
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  have hterm : ∀ p : {p : ℕ // p.Prime}, glFactor p (localGLMap p (diagGL u v)) =
      Real.sqrt (((p.1 ^ (u : ℕ).factorization p.1 : ℕ) : ℝ)⁻¹) *
        Real.sqrt (((p.1 ^ (v : ℕ).factorization p.1 : ℕ) : ℝ)⁻¹) /
        (((p.1 ^ (g : ℕ).factorization p.1 : ℕ) : ℝ)⁻¹) := fun p => by
    rw [glFactor_diagGL]
    change Real.sqrt ‖((u : ℕ) : ℚ_[p.1])‖ * Real.sqrt ‖((v : ℕ) : ℚ_[p.1])‖ /
      ‖((g : ℕ) : ℚ_[p.1])‖ = _
    rw [padic_norm_pnat, padic_norm_pnat, padic_norm_pnat]
  simp_rw [hterm]
  rw [Finset.prod_map]
  change (∏ x ∈ N.primeFactors.attach,
      Real.sqrt (((x.1 ^ (u : ℕ).factorization x.1 : ℕ) : ℝ)⁻¹) *
        Real.sqrt (((x.1 ^ (v : ℕ).factorization x.1 : ℕ) : ℝ)⁻¹) /
        (((x.1 ^ (g : ℕ).factorization x.1 : ℕ) : ℝ)⁻¹)) = _
  rw [Finset.prod_attach N.primeFactors (fun q =>
    Real.sqrt (((q ^ (u : ℕ).factorization q : ℕ) : ℝ)⁻¹) *
      Real.sqrt (((q ^ (v : ℕ).factorization q : ℕ) : ℝ)⁻¹) /
      (((q ^ (g : ℕ).factorization q : ℕ) : ℝ)⁻¹))]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
    prod_sqrt_nonneg _ _ (fun _ _ => by positivity),
    prod_sqrt_nonneg _ _ (fun _ _ => by positivity),
    Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib,
    prod_prime_pow_factorization_of_dvd hN u (dvd_mul_right _ _),
    prod_prime_pow_factorization_of_dvd hN v (dvd_mul_left _ _),
    prod_prime_pow_factorization_of_dvd hN g ((Nat.gcd_dvd_left _ _).trans (dvd_mul_right _ _))]
  have hu0 : (0 : ℝ) < u := by exact_mod_cast u.pos
  have hv0 : (0 : ℝ) < v := by exact_mod_cast v.pos
  have hg0 : (0 : ℝ) < g := by exact_mod_cast g.pos
  rw [Real.sqrt_inv, Real.sqrt_inv, ← mul_inv, ← Real.sqrt_mul hu0.le]
  have hgnat : ((g : ℕ) : ℝ) = (Nat.gcd (u : ℕ) v : ℝ) := by simp only [g, PNat.mk_coe]
  field_simp [hu0.ne', hv0.ne', hg0.ne']
  rw [hgnat]

/-- Exact finite Green product between `x_m` and `γ_{a/b} • x_n` for all `m, n, a, b : ℕ+`. -/
theorem finiteGreenProduct_torus_pos_rat (m n a b : ℕ+) :
    let q : ℚ := ((a : ℕ) : ℚ) / b
    have hq : q ≠ 0 := div_ne_zero (by exact_mod_cast a.ne_zero) (by exact_mod_cast b.ne_zero)
    finiteGreenProduct (originalDegreePoint m).2
        ((torusElem q hq : AdelicGroup) • originalDegreePoint n).2 =
      (Nat.gcd ((n : ℕ) * b ^ 2) ((m : ℕ) * a ^ 2) : ℝ) /
        Real.sqrt (((n : ℕ) * b ^ 2 : ℝ) * ((m : ℕ) * a ^ 2)) := by
  intro q hq
  let u : ℕ+ := ⟨(n : ℕ) * b ^ 2, Nat.mul_pos n.pos (pow_pos b.pos 2)⟩
  let v : ℕ+ := ⟨(m : ℕ) * a ^ 2, Nat.mul_pos m.pos (pow_pos a.pos 2)⟩
  have hscQ : (((m : ℕ) : ℚ) * a * b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast m.ne_zero) (by exact_mod_cast a.ne_zero))
      (by exact_mod_cast b.ne_zero)
  obtain ⟨uQ, huQ⟩ : ∃ u : ℚˣ, (u : ℚ) = ((m : ℕ) : ℚ) * a * b :=
    ⟨Units.mk0 (((m : ℕ) : ℚ) * a * b) hscQ, rfl⟩
  have hGL : (upperDegree m)⁻¹ *
      (SpecialLinearGroup.toGL (OppositeAdelic.diagonal q⁻¹ (inv_ne_zero hq)) * upperDegree n) *
      GeneralLinearGroup.scalar (Fin 2) uQ =
      diagGL u v := by
    have ha0 : ((a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast a.ne_zero
    have hb0 : ((b : ℕ) : ℚ) ≠ 0 := by exact_mod_cast b.ne_zero
    have h00 : ((b : ℕ) : ℚ) / (a : ℕ) * (n : ℕ) * (((m : ℕ) : ℚ) * a * b) =
        ((m : ℕ) : ℚ) * ((n : ℕ) * (b : ℕ) ^ 2) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff ha0]
      ring
    have h11 : ((a : ℕ) : ℚ) / (b : ℕ) * (((m : ℕ) : ℚ) * a * b) =
        ((m : ℕ) : ℚ) * (a : ℕ) ^ 2 := by
      rw [div_mul_eq_mul_div, div_eq_iff hb0]
      ring
    rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · simp [huQ, upperDegree, OppositeAdelic.diagonal, SpecialLinearGroup.toGL,
        diagGL, Matrix.mul_apply, Fin.sum_univ_two, u, q]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h00
    · simp [upperDegree, OppositeAdelic.diagonal, SpecialLinearGroup.toGL,
        diagGL, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [upperDegree, OppositeAdelic.diagonal, SpecialLinearGroup.toGL,
        diagGL, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [huQ, upperDegree, OppositeAdelic.diagonal, SpecialLinearGroup.toGL,
        diagGL, Matrix.mul_apply, Fin.sum_univ_two, v, q]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h11
  have hloc : ∀ p : {p : ℕ // p.Prime},
      localFactor p ((originalDegreePoint m).2.1 p)
        (((torusElem q hq : AdelicGroup) • originalDegreePoint n).2.1 p) =
        glFactor p (localGLMap p (diagGL u v)) := by
    intro p
    change localFactor p (principalVertex (upperDegree m) p)
      ((conjugateEmbedding (OppositeAdelic.diagonal q hq)).2 p •
        principalVertex (upperDegree n) p) = _
    rw [conjugateEmbedding_finite, weyl_conj_diagonal, localProj_toGL]
    change pglFactor p ((ProjGenLinGroup.mk (localGLMap p (upperDegree m)))⁻¹ *
      (ProjGenLinGroup.mk (localGLMap p
        (SpecialLinearGroup.toGL (OppositeAdelic.diagonal q⁻¹ (inv_ne_zero hq)))) *
        ProjGenLinGroup.mk (localGLMap p (upperDegree n)))) = _
    rw [← map_inv, ← map_mul, ← map_mul, pglFactor_mk, ← map_inv, ← map_mul, ← map_mul]
    let sc : (ℚ_[p.1])ˣ := Units.mk0 ((uQ : ℚ) : ℚ_[p.1]) (by exact_mod_cast uQ.ne_zero)
    rw [← glFactor_mul_scalar p _ sc]
    congr 1
    have hmap := congrArg (localGLMap p) hGL
    rw [map_mul, localGLMap_scalar] at hmap
    exact hmap
  unfold finiteGreenProduct
  simp_rw [hloc]
  rw [finprod_glFactor_diagGL u v]
  simp only [u, v, PNat.mk_coe]
  push_cast
  rfl

private theorem archProfile_log_sub {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    archProfile (Real.log v - Real.log u) = Real.sqrt (u * v) * v / (v ^ 2 - u ^ 2) := by
  have hv : 0 < v := hu.trans huv
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have he1 : Real.exp (-(Real.log v - Real.log u) / 2) = Real.sqrt u / Real.sqrt v := by
    apply (sq_eq_sq₀ (Real.exp_pos _).le (div_nonneg hsu.le hsv.le)).mp
    rw [sq, ← Real.exp_add, show -(Real.log v - Real.log u) / 2 +
        -(Real.log v - Real.log u) / 2 = Real.log (u / v) by
      rw [Real.log_div hu.ne' hv.ne']; ring,
      Real.exp_log (div_pos hu hv), div_pow, Real.sq_sqrt hu.le, Real.sq_sqrt hv.le]
  have he2 : Real.exp (-2 * (Real.log v - Real.log u)) = (u / v) ^ 2 := by
    rw [show -2 * (Real.log v - Real.log u) = (2 : ℕ) * Real.log (u / v) by
      rw [Real.log_div hu.ne' hv.ne']; push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (div_pos hu hv)]
  unfold archProfile
  rw [he1, he2, Real.sqrt_mul hu.le]
  have hden1 : 1 - (u / v) ^ 2 ≠ 0 := by
    have hlt : (u / v) ^ 2 < 1 := by
      have hr : u / v < 1 := (div_lt_one hv).mpr huv
      nlinarith [div_pos hu hv]
    linarith
  have hden2 : v ^ 2 - u ^ 2 ≠ 0 := by nlinarith
  have hvsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
  field_simp [hsv.ne', hv.ne', hden1, hden2]
  nlinarith [hvsq]

theorem archProfile_abs_log {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) :
    archProfile |Real.log v - Real.log u| =
      Real.sqrt (u * v) * max u v / |v ^ 2 - u ^ 2| := by
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · have hlog : 0 < Real.log v - Real.log u := sub_pos.mpr (Real.log_lt_log hu hlt)
    have hsq : 0 < v ^ 2 - u ^ 2 := by nlinarith
    rw [abs_of_pos hlog, max_eq_right hlt.le, abs_of_pos hsq]
    exact archProfile_log_sub hu hlt
  · have hlog : 0 < Real.log u - Real.log v := sub_pos.mpr (Real.log_lt_log hv hgt)
    have hsq : 0 < u ^ 2 - v ^ 2 := by nlinarith
    rw [abs_sub_comm, abs_of_pos hlog, max_eq_left hgt.le, abs_sub_comm (v ^ 2) (u ^ 2),
      abs_of_pos hsq, mul_comm u v]
    exact archProfile_log_sub hv hgt

/-- Exact archimedean action of `torusElem q` on `originalDegreePoint n`. -/
theorem torusElem_arch_smul (q : ℚ) (hq : q ≠ 0) (n : ℕ+) :
    ((torusElem q hq : AdelicGroup) • originalDegreePoint n).1 =
      degPoint ((q : ℝ) ^ 2 * n)
        (mul_pos (sq_pos_of_ne_zero (by exact_mod_cast hq)) (by exact_mod_cast n.pos)) := by
  change h3Act (conjugateEmbedding (OppositeAdelic.diagonal q hq)).1
    (degPoint ((n : ℕ) : ℝ) (by exact_mod_cast n.pos)) = _
  rw [conjugateEmbedding_arch]
  have hdiag : OppositeAdelic.archMap (OppositeAdelic.diagonal q hq) =
      diagSL2 (q : ℂ) (by exact_mod_cast hq) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [OppositeAdelic.archMap, OppositeAdelic.diagonal, diagSL2]
  rw [hdiag, h3Act_diag]
  apply degPoint_eq
  rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Master rational formula for the coupled critical product along `T(ℚ)`.**
Whenever `(m : ℕ) * b² ≠ (n : ℕ) * a²`, `adelicCriticalProduct x_m (γ_{a/b} • x_n)` is a purely
rational function of `(m, n, a, b)`. -/
theorem adelicCriticalProduct_torus_pos_rat (m n a b : ℕ+)
    (hne : (m : ℕ) * (b : ℕ) ^ 2 ≠ (n : ℕ) * (a : ℕ) ^ 2) :
    let q : ℚ := ((a : ℕ) : ℚ) / b
    have hq : q ≠ 0 := div_ne_zero (by exact_mod_cast a.ne_zero) (by exact_mod_cast b.ne_zero)
    adelicCriticalProduct (originalDegreePoint m)
        ((torusElem q hq : AdelicGroup) • originalDegreePoint n) =
      (Nat.gcd ((n : ℕ) * b ^ 2) ((m : ℕ) * a ^ 2) : ℝ) *
        max ((m : ℝ) * b ^ 2) ((n : ℝ) * a ^ 2) /
          |((n : ℝ) * a ^ 2) ^ 2 - ((m : ℝ) * b ^ 2) ^ 2| := by
  intro q hq
  unfold adelicCriticalProduct
  rw [torusElem_arch_smul, finiteGreenProduct_torus_pos_rat]
  change archProfile (h3Dist (degPoint ((m : ℕ) : ℝ) (by exact_mod_cast m.pos)) _) * _ = _
  rw [h3Dist_degPoint]
  set U : ℝ := (m : ℝ) * (b : ℝ) ^ 2
  set V : ℝ := (n : ℝ) * (a : ℝ) ^ 2
  have hU : 0 < U := by positivity
  have hV : 0 < V := by positivity
  have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
  have hUV_ne : U ≠ V := by dsimp only [U, V]; exact_mod_cast hne
  have hlog : Real.log ((q : ℝ) ^ 2 * (n : ℝ)) - Real.log (m : ℝ) =
      Real.log V - Real.log U := by
    have hqv : (q : ℝ) ^ 2 * (n : ℝ) = V / (b : ℝ) ^ 2 := by
      dsimp only [q, V]
      push_cast
      field_simp [hb2.ne']
    have hmu : (m : ℝ) = U / (b : ℝ) ^ 2 := by
      dsimp only [U]
      field_simp [hb2.ne']
    rw [hqv, hmu, Real.log_div hV.ne' hb2.ne', Real.log_div hU.ne' hb2.ne']
    ring
  rw [hlog, archProfile_abs_log hU hV hUV_ne]
  have hrt_eq : Real.sqrt (((n : ℕ) * (b : ℕ) ^ 2 : ℝ) * ((m : ℕ) * (a : ℕ) ^ 2)) =
      Real.sqrt (U * V) := by
    congr 1
    dsimp only [U, V]
    ring
  rw [hrt_eq]
  have hrt : 0 < Real.sqrt (U * V) := Real.sqrt_pos.mpr (mul_pos hU hV)
  have hUV2 : V ^ 2 ≠ U ^ 2 := fun h => hUV_ne ((sq_eq_sq₀ hU.le hV.le).mp h.symm)
  have hden : |V ^ 2 - U ^ 2| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hUV2)
  field_simp [hrt.ne', hden]

/-- On `CoupledOrbit.Primitive`, the diagonal torus evaluation of `adelicCriticalProduct`
coincides with `CoupledOrbit.term 2`. -/
theorem adelicCriticalProduct_primitive_eq_term_two (p : CoupledOrbit.Primitive) :
    let a : ℕ+ := ⟨p.val.1, p.property.1⟩
    let b : ℕ+ := ⟨p.val.2, p.property.1.trans p.property.2.1⟩
    let q : ℚ := ((a : ℕ) : ℚ) / b
    have hq : q ≠ 0 := div_ne_zero (by exact_mod_cast a.ne_zero) (by exact_mod_cast b.ne_zero)
    adelicCriticalProduct (originalDegreePoint 1)
        ((torusElem q hq : AdelicGroup) • originalDegreePoint 1) =
      CoupledOrbit.term 2 p := by
  intro a b q hq
  have hab : (a : ℕ) < b := p.property.2.1
  have hne : (1 : ℕ) * (b : ℕ) ^ 2 ≠ (1 : ℕ) * (a : ℕ) ^ 2 := by
    simp only [one_mul]
    exact ne_of_gt (Nat.pow_lt_pow_left hab two_ne_zero)
  rw [adelicCriticalProduct_torus_pos_rat 1 1 a b hne]
  simp only [PNat.one_coe, one_mul, Nat.cast_one]
  have hcop : Nat.gcd ((b : ℕ) ^ 2) ((a : ℕ) ^ 2) = 1 :=
    (p.property.2.2.symm.pow 2 2).gcd_eq_one
  have haR : (0 : ℝ) < a := by exact_mod_cast a.pos
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hbR : (0 : ℝ) < b := haR.trans habR
  have hsq_lt : (a : ℝ) ^ 2 < (b : ℝ) ^ 2 := by nlinarith
  have h4_lt : (a : ℝ) ^ 4 < (b : ℝ) ^ 4 := by nlinarith
  rw [hcop, Nat.cast_one, one_mul, max_eq_left hsq_lt.le,
    show ((a : ℝ) ^ 2) ^ 2 - ((b : ℝ) ^ 2) ^ 2 = (a : ℝ) ^ 4 - (b : ℝ) ^ 4 by ring,
    abs_sub_comm, abs_of_pos (sub_pos.mpr h4_lt)]
  unfold CoupledOrbit.term
  have hbR' : (0 : ℝ) < (p.val.2 : ℝ) := hbR
  rw [Real.rpow_neg hbR'.le, Real.rpow_two]
  simp only [a, b, PNat.mk_coe] at hbR ⊢
  have hden1 : (p.val.2 : ℝ) ^ 4 - (p.val.1 : ℝ) ^ 4 ≠ 0 := by
    simp only [a, b, PNat.mk_coe] at h4_lt
    exact (sub_pos.mpr h4_lt).ne'
  have hden2 : 1 - ((p.val.1 : ℝ) / p.val.2) ^ 4 ≠ 0 := by
    simp only [a, b, PNat.mk_coe] at h4_lt
    have hr : ((p.val.1 : ℝ) / p.val.2) ^ 4 < 1 := by
      rw [div_pow]
      exact (div_lt_one (by positivity)).mpr h4_lt
    linarith
  field_simp [hbR.ne', hden1, hden2]

/-- **Identity evaluation erases prime contacts.** Between distinct degree points `x_m` and `x_n`,
`adelicCriticalProduct x_m x_n = gcd(m, n) * max(m, n) / |n² - m²|`, a smooth rational function
of `(m, n)` with no prime von Mangoldt weights `Λ(n/m)`. -/
theorem adelicCriticalProduct_degree_eq {m n : ℕ+} (hmn : m ≠ n) :
    adelicCriticalProduct (originalDegreePoint m) (originalDegreePoint n) =
      (Nat.gcd (m : ℕ) n : ℝ) * max (m : ℝ) n / |(n : ℝ) ^ 2 - (m : ℝ) ^ 2| := by
  have h1 : (torusElem 1 one_ne_zero : AdelicGroup) • originalDegreePoint n =
      originalDegreePoint n := by
    have hd1 : OppositeAdelic.diagonal 1 one_ne_zero = 1 := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [OppositeAdelic.diagonal]
    change conjugateEmbedding (OppositeAdelic.diagonal 1 one_ne_zero) • _ = _
    rw [hd1, map_one, one_smul]
  have hne : (m : ℕ) * (1 : ℕ) ^ 2 ≠ (n : ℕ) * (1 : ℕ) ^ 2 := by
    intro h
    simp only [one_pow, mul_one] at h
    exact hmn (Subtype.ext h)
  have hrat := adelicCriticalProduct_torus_pos_rat m n 1 1 hne
  simp only [PNat.one_coe, Nat.cast_one, div_one, one_pow, mul_one] at hrat
  rwa [h1, Nat.gcd_comm] at hrat

theorem adelicCriticalProduct_one_degree_eq {n : ℕ+} (hn : 1 < (n : ℕ)) :
    adelicCriticalProduct (originalDegreePoint 1) (originalDegreePoint n) =
      (n : ℝ) / ((n : ℝ) ^ 2 - 1) := by
  have hne : (1 : ℕ+) ≠ n := fun h => by
    have h1 := congrArg Subtype.val h
    change 1 = (n : ℕ) at h1
    omega
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  rw [adelicCriticalProduct_degree_eq hne]
  simp only [PNat.one_coe, Nat.gcd_one_left, Nat.cast_one, one_mul, max_eq_right hnR.le,
    one_pow, abs_of_pos (by nlinarith : (0 : ℝ) < (n : ℝ) ^ 2 - 1)]

/-! ## 4. Interior square-ratio collisions, Pell non-decay, and universal divergence -/

/-- **Interior archimedean collision of distinct degree classes.** For `k ≥ 2`, `[x_m] ≠ [x_{m k²}]`
on `X`, yet at `q = 1 / k ∈ ℚˣ` their `ℍ³` coordinates coincide (`h3Dist = 0`) while the finite
Green product remains strictly positive `= k⁻²`. -/
theorem offDiag_torus_arch_collision (m : ℕ+) {k : ℕ+} (hk : 2 ≤ (k : ℕ)) :
    let mk2 : ℕ+ := ⟨(m : ℕ) * k ^ 2, Nat.mul_pos m.pos (pow_pos k.pos 2)⟩
    let q : ℚ := 1 / ((k : ℕ) : ℚ)
    have hq : q ≠ 0 := one_div_ne_zero (by exact_mod_cast k.ne_zero)
    originalDegreeClass m ≠ originalDegreeClass mk2 ∧
      ((torusElem q hq : AdelicGroup) • originalDegreePoint mk2).1 =
        (originalDegreePoint m).1 ∧
      finiteGreenProduct (originalDegreePoint m).2
        ((torusElem q hq : AdelicGroup) • originalDegreePoint mk2).2 =
        ((k : ℝ) ^ 2)⁻¹ := by
  intro mk2 q hq
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have hm_eq := congrArg Subtype.val (originalDegreeClass_injective heq)
    change (m : ℕ) = (m : ℕ) * (k : ℕ) ^ 2 at hm_eq
    have hk2 : 4 ≤ (k : ℕ) ^ 2 := by nlinarith
    have hm_pos : 0 < (m : ℕ) := m.pos
    nlinarith
  · rw [torusElem_arch_smul]
    change _ = degPoint ((m : ℕ) : ℝ) (by exact_mod_cast m.pos)
    apply degPoint_eq
    have hk0 : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
    simp only [q, mk2, PNat.mk_coe]
    push_cast
    field_simp [hk0]
  · have hfg := finiteGreenProduct_torus_pos_rat m mk2 1 k
    simp only [PNat.one_coe, Nat.cast_one, one_pow, mul_one, mk2, PNat.mk_coe] at hfg
    rw [hfg]
    have hgcd : Nat.gcd ((m : ℕ) * (k : ℕ) ^ 2 * (k : ℕ) ^ 2) (m : ℕ) = m :=
      Nat.gcd_eq_right ⟨(k : ℕ) ^ 2 * (k : ℕ) ^ 2, by ring⟩
    have hmR : (0 : ℝ) < m := by exact_mod_cast m.pos
    have hkR : (0 : ℝ) < k := by exact_mod_cast k.pos
    have hsq : Real.sqrt (((((m : ℕ) * (k : ℕ) ^ 2 : ℕ) : ℝ) * (k : ℝ) ^ 2) * (m : ℝ)) =
        (m : ℝ) * (k : ℝ) ^ 2 := by
      push_cast
      rw [show (m : ℝ) * (k : ℝ) ^ 2 * (k : ℝ) ^ 2 * (m : ℝ) = ((m : ℝ) * (k : ℝ) ^ 2) ^ 2 by
        ring, Real.sqrt_sq (by positivity)]
    rw [hgcd, hsq]
    field_simp [hmR.ne', hkR.ne']

/-- **Pell lower bound for any positive Pell solution.** Whenever `X² - m n Y² = 1` (`X, Y : ℕ+`),
at `q = (m Y) / X` the off-diagonal coupled product satisfies
`adelicCriticalProduct x_m (γ_q • x_n) > 1 / (2 m)`. -/
theorem adelicCriticalProduct_pell_gt_half_inv (m n X Y : ℕ+)
    (hpell : (X : ℕ) ^ 2 = 1 + (m : ℕ) * n * (Y : ℕ) ^ 2) :
    let q : ℚ := (((m : ℕ) * Y : ℕ) : ℚ) / X
    have hq : q ≠ 0 := div_ne_zero (by exact_mod_cast Nat.mul_ne_zero m.ne_zero Y.ne_zero)
      (by exact_mod_cast X.ne_zero)
    1 / (2 * (m : ℝ)) < adelicCriticalProduct (originalDegreePoint m)
      ((torusElem q hq : AdelicGroup) • originalDegreePoint n) := by
  intro q hq
  let a : ℕ+ := ⟨(m : ℕ) * Y, Nat.mul_pos m.pos Y.pos⟩
  have hUV : (n : ℕ) * (a : ℕ) ^ 2 + (m : ℕ) = (m : ℕ) * (X : ℕ) ^ 2 := by
    simp only [a, PNat.mk_coe]
    calc (n : ℕ) * ((m : ℕ) * Y) ^ 2 + m
        = (m : ℕ) * (1 + (m : ℕ) * n * (Y : ℕ) ^ 2) := by ring
      _ = (m : ℕ) * (X : ℕ) ^ 2 := by rw [← hpell]
  have hne : (m : ℕ) * (X : ℕ) ^ 2 ≠ (n : ℕ) * (a : ℕ) ^ 2 := by
    have hm_pos := m.pos
    omega
  have hval := adelicCriticalProduct_torus_pos_rat m n a X hne
  simp only [a, PNat.mk_coe] at hval hUV
  change 1 / (2 * (m : ℝ)) <
    adelicCriticalProduct (originalDegreePoint m)
      ((torusElem ((((m : ℕ) * Y : ℕ) : ℚ) / X) hq : AdelicGroup) • originalDegreePoint n)
  rw [hval]
  have hUV_R : (n : ℝ) * (((m : ℕ) * (Y : ℕ) : ℕ) : ℝ) ^ 2 + (m : ℝ) =
      (m : ℝ) * (X : ℝ) ^ 2 := by exact_mod_cast hUV
  have hmR : (0 : ℝ) < m := by exact_mod_cast m.pos
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast X.pos
  have hgcd_pos : 1 ≤ (Nat.gcd ((n : ℕ) * (X : ℕ) ^ 2) ((m : ℕ) * ((m : ℕ) * Y) ^ 2) : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left _ (Nat.mul_pos n.pos (pow_pos X.pos 2))
  have hlt_arch : (n : ℝ) * (((m : ℕ) * (Y : ℕ) : ℕ) : ℝ) ^ 2 < (m : ℝ) * (X : ℝ) ^ 2 := by
    linarith
  have hdiff : ((m : ℝ) * (X : ℝ) ^ 2) ^ 2 -
      ((n : ℝ) * (((m : ℕ) * (Y : ℕ) : ℕ) : ℝ) ^ 2) ^ 2 =
      (m : ℝ) ^ 2 * (2 * (X : ℝ) ^ 2 - 1) := by
    have hsub : (n : ℝ) * (((m : ℕ) * (Y : ℕ) : ℕ) : ℝ) ^ 2 =
        (m : ℝ) * (X : ℝ) ^ 2 - (m : ℝ) := by linarith [hUV_R]
    rw [hsub]
    ring
  have h2X_pos : 0 < 2 * (X : ℝ) ^ 2 - 1 := by nlinarith [hXR]
  have hden_pos : 0 < (m : ℝ) ^ 2 * (2 * (X : ℝ) ^ 2 - 1) := by positivity
  rw [max_eq_left hlt_arch.le, abs_sub_comm, abs_of_pos (by linarith [hdiff, hden_pos]), hdiff]
  calc 1 / (2 * (m : ℝ))
      < (m : ℝ) * (X : ℝ) ^ 2 / ((m : ℝ) ^ 2 * (2 * (X : ℝ) ^ 2 - 1)) := by
        apply (div_lt_div_iff₀ (by positivity) hden_pos).mpr
        nlinarith [hmR, hXR]
    _ ≤ (Nat.gcd ((n : ℕ) * (X : ℕ) ^ 2) ((m : ℕ) * ((m : ℕ) * Y) ^ 2) : ℝ) *
          ((m : ℝ) * (X : ℝ) ^ 2) / ((m : ℝ) ^ 2 * (2 * (X : ℝ) ^ 2 - 1)) := by
        apply div_le_div_of_nonneg_right _ hden_pos.le
        nlinarith [hgcd_pos, hmR, hXR]

/-- **Exact Pell value at `(1, 2)`.** Whenever `X² - 2 Y² = 1` (`X, Y : ℕ+`),
`adelicCriticalProduct x_1 (γ_{Y / X} • x_2) = 2 X² / (2 X² - 1) > 1`. -/
theorem adelicCriticalProduct_one_two_pell_eq (X Y : ℕ+)
    (hpell : (X : ℕ) ^ 2 = 1 + 2 * (Y : ℕ) ^ 2) :
    let q : ℚ := ((Y : ℕ) : ℚ) / X
    have hq : q ≠ 0 := div_ne_zero (by exact_mod_cast Y.ne_zero) (by exact_mod_cast X.ne_zero)
    adelicCriticalProduct (originalDegreePoint 1)
        ((torusElem q hq : AdelicGroup) • originalDegreePoint 2) =
      2 * (X : ℝ) ^ 2 / (2 * (X : ℝ) ^ 2 - 1) ∧
    1 < 2 * (X : ℝ) ^ 2 / (2 * (X : ℝ) ^ 2 - 1) := by
  intro q hq
  have h2_coe : ((2 : ℕ+) : ℕ) = 2 := rfl
  have hne : (1 : ℕ) * (X : ℕ) ^ 2 ≠ 2 * (Y : ℕ) ^ 2 := by omega
  have hval := adelicCriticalProduct_torus_pos_rat 1 2 Y X hne
  simp only [PNat.one_coe, h2_coe, one_mul, Nat.cast_one, Nat.cast_ofNat] at hval
  have hevenY : 2 ∣ (Y : ℕ) ^ 2 := by
    have hmod : ((X : ℕ) ^ 2) % 4 = 1 := by
      have hodd : (X : ℕ) % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one (X : ℕ) with h0 | h1
        · exfalso
          have hdiv : (X : ℕ) = 2 * ((X : ℕ) / 2) := by omega
          have hsq : (X : ℕ) ^ 2 = 4 * ((X : ℕ) / 2) ^ 2 := by
            conv_lhs => rw [hdiv]
            ring
          omega
        · exact h1
      have hdiv : (X : ℕ) = 2 * ((X : ℕ) / 2) + 1 := by omega
      have hsq : (X : ℕ) ^ 2 = 4 * (((X : ℕ) / 2) ^ 2 + (X : ℕ) / 2) + 1 := by
        conv_lhs => rw [hdiv]
        ring
      omega
    omega
  have hcop : Nat.Coprime ((X : ℕ) ^ 2) ((Y : ℕ) ^ 2) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hd1 : Nat.gcd ((X : ℕ) ^ 2) ((Y : ℕ) ^ 2) ∣ 1 := by
      have hdX := Nat.gcd_dvd_left ((X : ℕ) ^ 2) ((Y : ℕ) ^ 2)
      have hdY := dvd_mul_of_dvd_right (Nat.gcd_dvd_right ((X : ℕ) ^ 2) ((Y : ℕ) ^ 2)) 2
      obtain ⟨kX, hkX⟩ := hdX
      obtain ⟨kY, hkY⟩ := hdY
      refine ⟨kX - kY, ?_⟩
      zify [show kY ≤ kX by nlinarith [Nat.gcd_pos_of_pos_left ((Y : ℕ) ^ 2) (pow_pos X.pos 2)]]
      linarith [hpell]
    exact Nat.eq_one_of_dvd_one hd1
  have hgcd : Nat.gcd (2 * (X : ℕ) ^ 2) ((Y : ℕ) ^ 2) = 2 := by
    obtain ⟨t, ht⟩ := hevenY
    rw [ht, Nat.gcd_mul_left]
    have hct : Nat.Coprime ((X : ℕ) ^ 2) t :=
      hcop.of_dvd_right ⟨2, by linarith⟩
    rw [hct.gcd_eq_one, mul_one]
  have hpellR : (X : ℝ) ^ 2 = 1 + 2 * (Y : ℝ) ^ 2 := by exact_mod_cast hpell
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast X.pos
  have hden : 0 < 2 * (X : ℝ) ^ 2 - 1 := by nlinarith
  constructor
  · change adelicCriticalProduct (originalDegreePoint 1)
      ((torusElem (((Y : ℕ) : ℚ) / X) hq : AdelicGroup) • originalDegreePoint 2) = _
    rw [hval, hgcd, Nat.cast_ofNat, max_eq_left (by linarith : 2 * (Y : ℝ) ^ 2 ≤ (X : ℝ) ^ 2),
      show (2 * (Y : ℝ) ^ 2) ^ 2 - ((X : ℝ) ^ 2) ^ 2 = -(2 * (X : ℝ) ^ 2 - 1) by nlinarith,
      abs_neg, abs_of_pos hden]
  · rw [one_lt_div hden]
    linarith

/-- Non-colliding rational torus displacements for `(m, n)`. -/
abbrev NonCollidingTorus (m n : ℕ+) : Type :=
  {q : ℚˣ // ((torusElem q.val q.ne_zero : AdelicGroup) • originalDegreePoint n).1 ≠
    (originalDegreePoint m).1}

/-- **Universal off-diagonal torus divergence.** For *every* pair of degrees `m, n : ℕ+`, the
coupled local critical product `adelicCriticalProduct x_m (γ_q • x_n)` is non-summable over
non-colliding `q ∈ ℚˣ`: by harmonic accumulation near the square-root displacement when `m * n`
is a square, and by Pell unit non-decay when `m * n` is not a square. -/
theorem not_summable_adelicCriticalProduct_torus_noncolliding (m n : ℕ+) :
    ¬ Summable (fun q : NonCollidingTorus m n =>
      adelicCriticalProduct (originalDegreePoint m)
        ((torusElem q.1.val q.1.ne_zero : AdelicGroup) • originalDegreePoint n)) := by
  by_cases hsq : IsSquare ((m : ℕ) * n)
  · obtain ⟨s, hs⟩ := hsq
    have hs_pos : 0 < s := by
      by_contra h0
      have hs0 : s = 0 := by omega
      rw [hs0, mul_zero] at hs
      exact (mul_ne_zero m.ne_zero n.ne_zero) hs
    let ak (k : ℕ) : ℕ+ := ⟨(m : ℕ) * (k + 1), Nat.mul_pos m.pos (Nat.succ_pos k)⟩
    let bk (k : ℕ) : ℕ+ := ⟨s * (k + 1) + 1, Nat.succ_pos _⟩
    let qk (k : ℕ) : ℚˣ := Units.mk0 (((ak k : ℕ) : ℚ) / (bk k : ℕ))
      (div_ne_zero (by exact_mod_cast (ak k).ne_zero) (by exact_mod_cast (bk k).ne_zero))
    have hUV_k : ∀ k : ℕ, (n : ℕ) * (ak k : ℕ) ^ 2 +
        (2 * (m : ℕ) * s * (k + 1) + m) = (m : ℕ) * (bk k : ℕ) ^ 2 := by
      intro k
      simp only [ak, bk, PNat.mk_coe]
      have hss : (m : ℕ) * n = s ^ 2 := hs.trans (sq s).symm
      calc (n : ℕ) * ((m : ℕ) * (k + 1)) ^ 2 + (2 * (m : ℕ) * s * (k + 1) + m)
          = (m : ℕ) * ((m : ℕ) * n) * (k + 1) ^ 2 + 2 * (m : ℕ) * s * (k + 1) + m := by ring
        _ = (m : ℕ) * s ^ 2 * (k + 1) ^ 2 + 2 * (m : ℕ) * s * (k + 1) + m := by rw [hss]
        _ = (m : ℕ) * (s * (k + 1) + 1) ^ 2 := by ring
    have hnc : ∀ k : ℕ,
        ((torusElem (qk k).val (qk k).ne_zero : AdelicGroup) • originalDegreePoint n).1 ≠
          (originalDegreePoint m).1 := by
      intro k heq
      rw [torusElem_arch_smul] at heq
      have ht := congrArg H3.t heq
      change ((qk k).val : ℝ) ^ 2 * (n : ℝ) = (m : ℝ) at ht
      have hb0 : ((bk k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (bk k).ne_zero
      have hmul : (n : ℝ) * ((ak k : ℕ) : ℝ) ^ 2 = (m : ℝ) * ((bk k : ℕ) : ℝ) ^ 2 := by
        simp only [qk, Units.val_mk0] at ht
        push_cast at ht
        field_simp [hb0] at ht
        linarith
      have hnat : (n : ℕ) * (ak k : ℕ) ^ 2 = (m : ℕ) * (bk k : ℕ) ^ 2 := by exact_mod_cast hmul
      have hm_pos := m.pos
      have := hUV_k k
      omega
    let seq (k : ℕ) : NonCollidingTorus m n := ⟨qk k, hnc k⟩
    have hinj : Function.Injective seq := by
      intro k l h
      have hq_eq : ((ak k : ℕ) : ℚ) / (bk k : ℕ) = ((ak l : ℕ) : ℚ) / (bk l : ℕ) :=
        congrArg (fun x : NonCollidingTorus m n => x.1.val) h
      have hbk0 : ((bk k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (bk k).ne_zero
      have hbl0 : ((bk l : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (bk l).ne_zero
      have hcrossQ : ((ak k : ℕ) : ℚ) * (bk l : ℕ) = ((ak l : ℕ) : ℚ) * (bk k : ℕ) :=
        (div_eq_div_iff hbk0 hbl0).mp hq_eq
      have hcross : (ak k : ℕ) * (bk l : ℕ) = (ak l : ℕ) * (bk k : ℕ) := by
        exact_mod_cast hcrossQ
      simp only [ak, bk, PNat.mk_coe] at hcross
      have hcancel := Nat.eq_of_mul_eq_mul_left m.pos
        (show (m : ℕ) * ((k + 1) * (s * (l + 1) + 1)) =
            (m : ℕ) * ((l + 1) * (s * (k + 1) + 1)) by linarith [hcross])
      nlinarith
    intro hsum
    have hsub := hsum.comp_injective hinj
    have hbound : ∀ k : ℕ, 1 / (6 * (m : ℝ) * s * ((k : ℝ) + 1)) ≤
        adelicCriticalProduct (originalDegreePoint m)
          ((torusElem (seq k).1.val (seq k).1.ne_zero : AdelicGroup) • originalDegreePoint n) := by
      intro k
      have hne : (m : ℕ) * (bk k : ℕ) ^ 2 ≠ (n : ℕ) * (ak k : ℕ) ^ 2 := by
        have := hUV_k k
        have := m.pos
        omega
      change 1 / (6 * (m : ℝ) * s * ((k : ℝ) + 1)) ≤
        adelicCriticalProduct (originalDegreePoint m)
          ((torusElem (((ak k : ℕ) : ℚ) / (bk k : ℕ)) _ : AdelicGroup) • originalDegreePoint n)
      rw [adelicCriticalProduct_torus_pos_rat m n (ak k) (bk k) hne]
      set U : ℝ := (m : ℝ) * ((bk k : ℕ) : ℝ) ^ 2
      set V : ℝ := (n : ℝ) * ((ak k : ℕ) : ℝ) ^ 2
      set D : ℝ := 2 * (m : ℝ) * s * ((k : ℝ) + 1) + m
      have hUV_R : V + D = U := by
        dsimp only [U, V, D]
        exact_mod_cast hUV_k k
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast m.pos
      have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs_pos
      have hD_pos : 0 < D := by positivity
      have hU_pos : 0 < U := by
        have : 0 ≤ V := by positivity
        linarith
      have hV_nonneg : 0 ≤ V := by positivity
      have hD_le : D ≤ 3 * (m : ℝ) * s * ((k : ℝ) + 1) := by
        dsimp only [D]
        have hms : (m : ℝ) ≤ (m : ℝ) * s * ((k : ℝ) + 1) := by
          have : (1 : ℝ) ≤ (s : ℝ) * ((k : ℝ) + 1) := by nlinarith
          nlinarith
        linarith
      have hdiff_pos : 0 < U ^ 2 - V ^ 2 := by nlinarith
      have hdiff_le : U ^ 2 - V ^ 2 ≤ (6 * (m : ℝ) * s * ((k : ℝ) + 1)) * U := by
        have h1 : U ^ 2 - V ^ 2 = D * (U + V) := by nlinarith
        have h2 : U + V ≤ 2 * U := by linarith
        nlinarith
      have hgcd_ge : (1 : ℝ) ≤
          (Nat.gcd ((n : ℕ) * (bk k : ℕ) ^ 2) ((m : ℕ) * (ak k : ℕ) ^ 2) : ℝ) := by
        exact_mod_cast Nat.gcd_pos_of_pos_left _ (Nat.mul_pos n.pos (pow_pos (bk k).pos 2))
      rw [max_eq_left (by linarith : V ≤ U), abs_sub_comm, abs_of_pos hdiff_pos]
      calc 1 / (6 * (m : ℝ) * s * ((k : ℝ) + 1))
          = U / ((6 * (m : ℝ) * s * ((k : ℝ) + 1)) * U) := by
            field_simp [hU_pos.ne', (show (6 : ℝ) * m * s * (k + 1) ≠ 0 by positivity)]
        _ ≤ U / (U ^ 2 - V ^ 2) :=
            div_le_div_of_nonneg_left hU_pos.le hdiff_pos hdiff_le
        _ ≤ (Nat.gcd ((n : ℕ) * (bk k : ℕ) ^ 2) ((m : ℕ) * (ak k : ℕ) ^ 2) : ℝ) * U /
              (U ^ 2 - V ^ 2) := by
            apply div_le_div_of_nonneg_right _ hdiff_pos.le
            nlinarith [hgcd_ge, hU_pos]
    have hharm_scaled : Summable (fun k : ℕ => 1 / (6 * (m : ℝ) * s * ((k : ℝ) + 1))) :=
      hsub.of_nonneg_of_le (fun k => by positivity) hbound
    have hmR : (0 : ℝ) < m := by exact_mod_cast m.pos
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs_pos
    have hharm1 : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-1 : ℝ)) := by
      have hm := hharm_scaled.mul_left (6 * (m : ℝ) * s)
      refine hm.congr fun k => ?_
      push_cast
      rw [Real.rpow_neg_one]
      field_simp [hmR.ne', hsR.ne']
    have hharm0 := (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) ^ (-1 : ℝ)) 1).mp hharm1
    exact lt_irrefl (-1 : ℝ) (Real.summable_nat_rpow.mp hharm0)
  · let d : ℤ := (m : ℤ) * n
    have hd_pos : 0 < d := mul_pos (by exact_mod_cast m.pos) (by exact_mod_cast n.pos)
    have hd_nsq : ¬ IsSquare d := by
      rintro ⟨z, hz⟩
      apply hsq
      refine ⟨z.natAbs, ?_⟩
      have hsqZ : ((m : ℕ) * n : ℤ) = (z.natAbs : ℤ) * z.natAbs := by
        calc ((m : ℕ) * n : ℤ) = d := rfl
          _ = z * z := hz
          _ = (z.natAbs : ℤ) * z.natAbs := by
            simpa only [sq] using (Int.natAbs_sq z).symm
      exact_mod_cast hsqZ
    obtain ⟨s₀, hs₀⟩ := Pell.IsFundamental.exists_of_not_isSquare hd_pos hd_nsq
    let sk (k : ℕ) : Pell.Solution₁ d := s₀ ^ ((k + 1 : ℕ) : ℤ)
    have hxk_pos : ∀ k : ℕ, 0 < (sk k).x := fun k =>
      Pell.Solution₁.x_zpow_pos hs₀.x_pos _
    have hyk_pos : ∀ k : ℕ, 0 < (sk k).y := fun k =>
      Pell.Solution₁.y_zpow_pos hs₀.x_pos hs₀.2.1 (by omega)
    let Xk (k : ℕ) : ℕ+ := ⟨(sk k).x.toNat, Int.lt_toNat.mpr (hxk_pos k)⟩
    let Yk (k : ℕ) : ℕ+ := ⟨(sk k).y.toNat, Int.lt_toNat.mpr (hyk_pos k)⟩
    have hpell_k : ∀ k : ℕ, (Xk k : ℕ) ^ 2 = 1 + (m : ℕ) * n * (Yk k : ℕ) ^ 2 := by
      intro k
      have hpZ := (sk k).prop_x
      have hxZ : ((Xk k : ℕ) : ℤ) = (sk k).x := Int.toNat_of_nonneg (hxk_pos k).le
      have hyZ : ((Yk k : ℕ) : ℤ) = (sk k).y := Int.toNat_of_nonneg (hyk_pos k).le
      apply Nat.cast_injective (R := ℤ)
      push_cast
      rw [hxZ, hyZ]
      exact hpZ
    let qk (k : ℕ) : ℚˣ := Units.mk0 ((((m : ℕ) * Yk k : ℕ) : ℚ) / (Xk k : ℕ))
      (div_ne_zero (by exact_mod_cast Nat.mul_ne_zero m.ne_zero (Yk k).ne_zero)
        (by exact_mod_cast (Xk k).ne_zero))
    have hnc : ∀ k : ℕ,
        ((torusElem (qk k).val (qk k).ne_zero : AdelicGroup) • originalDegreePoint n).1 ≠
          (originalDegreePoint m).1 := by
      intro k heq
      rw [torusElem_arch_smul] at heq
      have ht := congrArg H3.t heq
      change ((qk k).val : ℝ) ^ 2 * (n : ℝ) = (m : ℝ) at ht
      have hX0 : ((Xk k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Xk k).ne_zero
      have hmul : (n : ℝ) * (((m : ℕ) * Yk k : ℕ) : ℝ) ^ 2 =
          (m : ℝ) * ((Xk k : ℕ) : ℝ) ^ 2 := by
        simp only [qk, Units.val_mk0] at ht
        push_cast at ht ⊢
        field_simp [hX0] at ht
        nlinarith [ht]
      have hnat : (n : ℕ) * ((m : ℕ) * Yk k) ^ 2 = (m : ℕ) * (Xk k : ℕ) ^ 2 := by
        exact_mod_cast hmul
      have hp := hpell_k k
      have hm_pos := m.pos
      nlinarith
    let seq (k : ℕ) : NonCollidingTorus m n := ⟨qk k, hnc k⟩
    have hinj : Function.Injective seq := by
      intro k l h
      have hq_eq : ((((m : ℕ) * Yk k : ℕ) : ℚ) / (Xk k : ℕ)) =
          ((((m : ℕ) * Yk l : ℕ) : ℚ) / (Xk l : ℕ)) :=
        congrArg (fun x : NonCollidingTorus m n => x.1.val) h
      have hXk0 : ((Xk k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Xk k).ne_zero
      have hXl0 : ((Xk l : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Xk l).ne_zero
      have hcrossQ : (((m : ℕ) * Yk k : ℕ) : ℚ) * (Xk l : ℕ) =
          (((m : ℕ) * Yk l : ℕ) : ℚ) * (Xk k : ℕ) :=
        (div_eq_div_iff hXk0 hXl0).mp hq_eq
      have hcross : ((m : ℕ) * Yk k) * (Xk l : ℕ) = ((m : ℕ) * Yk l) * (Xk k : ℕ) := by
        exact_mod_cast hcrossQ
      have hyx : (Yk k : ℕ) * (Xk l : ℕ) = (Yk l : ℕ) * (Xk k : ℕ) :=
        Nat.eq_of_mul_eq_mul_left m.pos (by linarith [hcross])
      have hsq_eq : (Yk k : ℕ) ^ 2 * (Xk l : ℕ) ^ 2 = (Yk l : ℕ) ^ 2 * (Xk k : ℕ) ^ 2 := by
        calc (Yk k : ℕ) ^ 2 * (Xk l : ℕ) ^ 2 = ((Yk k : ℕ) * (Xk l : ℕ)) ^ 2 := by ring
          _ = ((Yk l : ℕ) * (Xk k : ℕ)) ^ 2 := by rw [hyx]
          _ = (Yk l : ℕ) ^ 2 * (Xk k : ℕ) ^ 2 := by ring
      rw [hpell_k k, hpell_k l] at hsq_eq
      have hy_sq : (Yk k : ℕ) ^ 2 = (Yk l : ℕ) ^ 2 := by nlinarith
      have hy_nat : (Yk k : ℕ) = (Yk l : ℕ) := by nlinarith [(Yk k).pos, (Yk l).pos]
      have hy_int : (sk k).y = (sk l).y := by
        have hkZ : ((Yk k : ℕ) : ℤ) = (sk k).y := Int.toNat_of_nonneg (hyk_pos k).le
        have hlZ : ((Yk l : ℕ) : ℤ) = (sk l).y := Int.toNat_of_nonneg (hyk_pos l).le
        rw [← hkZ, ← hlZ, hy_nat]
      have hexp := hs₀.y_strictMono.injective hy_int
      omega
    intro hsum
    have htend := (hsum.comp_injective hinj).tendsto_atTop_zero
    have hmR : (0 : ℝ) < m := by exact_mod_cast m.pos
    have hc : 0 < 1 / (2 * (m : ℝ)) := by positivity
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨K, hK⟩ := htend (1 / (2 * (m : ℝ))) hc
    have hlt := hK K le_rfl
    have hgt : 1 / (2 * (m : ℝ)) <
        adelicCriticalProduct (originalDegreePoint m)
          ((torusElem (seq K).1.val (seq K).1.ne_zero : AdelicGroup) • originalDegreePoint n) :=
      adelicCriticalProduct_pell_gt_half_inv m n (Xk K) (Yk K) (hpell_k K)
    change dist (adelicCriticalProduct (originalDegreePoint m)
      ((torusElem (seq K).1.val (seq K).1.ne_zero : AdelicGroup) • originalDegreePoint n)) 0 < _
        at hlt
    rw [Real.dist_eq, sub_zero, abs_of_pos (hc.trans hgt)] at hlt
    exact lt_irrefl _ (hgt.trans hlt)

/-! ## 5. Torus non-invariance of naive rational height cutoffs -/

/-- Standard multiplicative Weil height `max(|num q|, den q)` on `ℚ`. -/
def weilHeight (q : ℚ) : ℕ :=
  max q.num.natAbs q.den

private theorem num_den_of_coprime_div {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) :
    (((a : ℚ) / b).num.natAbs = a) ∧ (((a : ℚ) / b).den = b) := by
  set r : ℚ := (a : ℚ) / b
  have hr_pos : 0 < r := div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hnum_pos : 0 < r.num := Rat.num_pos.mpr hr_pos
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hmulQ : (r.num : ℚ) * b = (a : ℚ) * r.den := by
    have h1 : r * b = a := div_mul_cancel₀ _ hbQ
    have h2 : r * r.den = r.num := Rat.mul_den_eq_num r
    calc (r.num : ℚ) * b = (r * r.den) * b := by rw [← h2]
      _ = (r * b) * r.den := by ring
      _ = (a : ℚ) * r.den := by rw [h1]
  have hmul : r.num.natAbs * b = a * r.den := by
    have hZ : r.num * (b : ℤ) = (a : ℤ) * r.den := by exact_mod_cast hmulQ
    have hn : (r.num.natAbs : ℤ) = r.num := Int.natAbs_of_nonneg hnum_pos.le
    rw [← hn] at hZ
    exact_mod_cast hZ
  have hd1 : r.num.natAbs ∣ a :=
    r.reduced.dvd_of_dvd_mul_right ⟨b, by linarith [hmul]⟩
  have hd2 : a ∣ r.num.natAbs :=
    hcop.dvd_of_dvd_mul_right ⟨r.den, by linarith [hmul]⟩
  have heq_a : r.num.natAbs = a := Nat.dvd_antisymm hd1 hd2
  rw [heq_a] at hmul
  exact ⟨heq_a, (mul_left_cancel₀ ha.ne' hmul).symm⟩

theorem weilHeight_eq_num_of_one_lt {q : ℚ} (hq : 1 < q) :
    weilHeight q = q.num.natAbs := by
  have hd_pos : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hltQ : (q.den : ℚ) < q.num := by
    have h1 := (mul_lt_mul_iff_left₀ hd_pos).mpr hq
    rwa [one_mul, Rat.mul_den_eq_num] at h1
  have hltZ : (q.den : ℤ) < q.num := by exact_mod_cast hltQ
  have hnum_pos : 0 < q.num := lt_trans (Nat.cast_pos.mpr q.den_pos) hltZ
  have hlt : q.den < q.num.natAbs := by
    have hZ : (q.den : ℤ) < (q.num.natAbs : ℤ) := by
      rwa [Int.natAbs_of_nonneg hnum_pos.le]
    exact_mod_cast hZ
  exact max_eq_left hlt.le

/-- **Prime torus shift distorts `weilHeight` conditionally on denominator divisibility.** -/
theorem weilHeight_mul_prime_of_one_lt {p : ℕ} (hp : p.Prime) {q : ℚ} (hq : 1 < q) :
    weilHeight ((p : ℚ) * q) =
      if p ∣ q.den then weilHeight q else p * weilHeight q := by
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hpq1 : 1 < (p : ℚ) * q := by nlinarith
  rw [weilHeight_eq_num_of_one_lt hpq1, weilHeight_eq_num_of_one_lt hq]
  have hq_pos : 0 < q := zero_lt_one.trans hq
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq_pos
  have ha_pos : 0 < q.num.natAbs := Int.natAbs_pos.mpr hnum_pos.ne'
  have hnumZ : (q.num : ℚ) = (q.num.natAbs : ℚ) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg hnum_pos.le]
  have hq_eq : q = (q.num.natAbs : ℚ) / q.den := by
    conv_lhs => rw [← Rat.num_div_den q, hnumZ]
  by_cases hdvd : p ∣ q.den
  · rw [if_pos hdvd]
    let d' : ℕ := q.den / p
    have hden_eq : q.den = p * d' := (Nat.mul_div_cancel' hdvd).symm
    have hd'_pos : 0 < d' := by
      have := q.den_pos
      have := hp.pos
      nlinarith
    have hcop' : Nat.Coprime q.num.natAbs d' :=
      q.reduced.of_dvd_right ⟨p, by linarith⟩
    have hpq_eq : (p : ℚ) * q = (q.num.natAbs : ℚ) / d' := by
      conv_lhs => rw [hq_eq, hden_eq]
      push_cast
      have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp [hpQ]
    rw [hpq_eq]
    exact (num_den_of_coprime_div ha_pos hd'_pos hcop').1
  · rw [if_neg hdvd]
    have hcop_p : Nat.Coprime p q.den := hp.coprime_iff_not_dvd.mpr hdvd
    have hcop_mul : Nat.Coprime (p * q.num.natAbs) q.den := hcop_p.mul_left q.reduced
    have hpq_eq : (p : ℚ) * q = ((p * q.num.natAbs : ℕ) : ℚ) / q.den := by
      conv_lhs => rw [hq_eq]
      push_cast
      ring
    rw [hpq_eq]
    exact (num_den_of_coprime_div (Nat.mul_pos hp.pos ha_pos) q.den_pos hcop_mul).1

/-- **Strict non-invariance of every height cutoff `N ≥ 5` under prime torus shifts.** -/
theorem weilHeight_ball_mul_prime_ssubset {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) :
    {q : ℚ | 1 < q ∧ weilHeight ((p : ℚ) * q) < N} ⊂
      {q : ℚ | 1 < q ∧ weilHeight q < N} := by
  refine ⟨?_, ?_⟩
  · intro q ⟨hq1, hlt⟩
    refine ⟨hq1, lt_of_le_of_lt ?_ hlt⟩
    rw [weilHeight_mul_prime_of_one_lt hp hq1]
    split_ifs
    · exact le_rfl
    · exact Nat.le_mul_of_pos_left _ hp.pos
  · intro hsub
    let m : ℕ := if p ∣ (N - 2) then N - 3 else N - 2
    have hm_ge : N - 3 ≤ m := by dsimp only [m]; split_ifs <;> omega
    have hm_pos : 0 < m := by omega
    have hndvd : ¬ p ∣ m := by
      dsimp only [m]
      split_ifs with hd2
      · intro hd3
        have hsub1 : (N - 2) - (N - 3) = 1 := by omega
        have hd1 : p ∣ (N - 2) - (N - 3) := Nat.dvd_sub hd2 hd3
        rw [hsub1] at hd1
        exact hp.not_dvd_one hd1
      · exact hd2
    let q : ℚ := ((m + 1 : ℕ) : ℚ) / m
    have hq1 : 1 < q := by
      dsimp only [q]
      rw [one_lt_div (by exact_mod_cast hm_pos)]
      exact_mod_cast Nat.lt_succ_self m
    have hcop : Nat.Coprime (m + 1) m :=
      (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right m)).symm
    obtain ⟨hnum, hden⟩ := num_den_of_coprime_div (Nat.succ_pos m) hm_pos hcop
    have hwh : weilHeight q = m + 1 := by
      rw [weilHeight_eq_num_of_one_lt hq1]
      exact hnum
    have hq_in : q ∈ {r : ℚ | 1 < r ∧ weilHeight r < N} := by
      refine ⟨hq1, ?_⟩
      rw [hwh]
      dsimp only [m]
      split_ifs <;> omega
    have hq_out := (hsub hq_in).2
    rw [weilHeight_mul_prime_of_one_lt hp hq1, hden, if_neg hndvd, hwh] at hq_out
    have hp2 := hp.two_le
    have hNm : N ≤ m + 3 := by omega
    nlinarith

#print axioms adelicCriticalProduct_smul
#print axioms adelicDegreeShift_comm_torus
#print axioms adelicCriticalProduct_torus_diag_eq
#print axioms localFactor_upperDegree_eq_treeGreen
#print axioms adelicCriticalProduct_torus_pos_rat
#print axioms adelicCriticalProduct_degree_eq
#print axioms offDiag_torus_arch_collision
#print axioms adelicCriticalProduct_pell_gt_half_inv
#print axioms adelicCriticalProduct_one_two_pell_eq
#print axioms not_summable_adelicCriticalProduct_torus_noncolliding
#print axioms weilHeight_ball_mul_prime_ssubset

end GaloisForLFunctions.HyperbolicArakelovTheory.CoupledProductObstruction
