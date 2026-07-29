import GaloisForLFunctions.HTGeometry.ConstrainedCauchyJetControllability
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Triangular conversion from Nevanlinna jets to Cauchy-power packets

For a regular Nevanlinna kernel `a(w) * (tau - q(w))⁻¹`, every finite packet of genuine
`w`-derivatives is an invertible lower-triangular linear image of the parameter Cauchy powers.
The diagonal is `r! * a(z) * (deriv q z)^r`.  Taking products over finitely many nodes upgrades
finite constrained Cauchy controllability to genuine Nevanlinna-jet controllability.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex
open Topology
open scoped BigOperators

noncomputable section

/-- Recursive coefficient of the parameter Cauchy power of order `k + 1` in the `r`-th genuine
Nevanlinna jet. -/
noncomputable def nevanlinnaJetCoeff (a q : ℂ → ℂ) : ℕ → ℕ → ℂ → ℂ
  | 0, k => if k = 0 then a else 0
  | r + 1, k => fun z =>
      deriv (nevanlinnaJetCoeff a q r k) z +
        if k = 0 then 0 else
          (k : ℂ) * deriv q z * nevanlinnaJetCoeff a q r (k - 1) z

/-- Smooth entire input data produce smooth recursive jet coefficients. -/
theorem contDiff_nevanlinnaJetCoeff
    {a q : ℂ → ℂ} (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q) :
    ∀ r k, ContDiff ℂ ⊤ (nevanlinnaJetCoeff a q r k) := by
  intro r
  induction r with
  | zero =>
      intro k
      simp only [nevanlinnaJetCoeff]
      split
      · exact ha
      · exact contDiff_const
  | succ r ih =>
      intro k
      simp only [nevanlinnaJetCoeff]
      apply ContDiff.add
      · simpa using (ih k).deriv'
      · split
        · exact contDiff_const
        · exact (contDiff_const.mul (by simpa using hq.deriv')).mul (ih (k - 1))

/-- The coefficient array is lower triangular. -/
theorem nevanlinnaJetCoeff_eq_zero_of_lt
    (a q : ℂ → ℂ) : ∀ {r k : ℕ}, r < k → nevanlinnaJetCoeff a q r k = 0 := by
  intro r
  induction r with
  | zero =>
      intro k hk
      funext z
      simp [nevanlinnaJetCoeff, Nat.ne_zero_of_lt hk]
  | succ r ih =>
      intro k hk
      have hk0 : k ≠ 0 := by omega
      have hrk : r < k := by omega
      have hrpred : r < k - 1 := by omega
      rw [nevanlinnaJetCoeff]
      rw [ih hrk, ih hrpred]
      ext z
      simp [hk0]

/-- The exact diagonal of the Nevanlinna jet conversion. -/
theorem nevanlinnaJetCoeff_diagonal
    {a q : ℂ → ℂ} : ∀ r z,
    nevanlinnaJetCoeff a q r r z =
      (r.factorial : ℂ) * a z * (deriv q z) ^ r := by
  intro r
  induction r with
  | zero =>
      intro z
      simp [nevanlinnaJetCoeff]
  | succ r ih =>
      intro z
      rw [nevanlinnaJetCoeff]
      have hzero := nevanlinnaJetCoeff_eq_zero_of_lt a q (Nat.lt_succ_self r)
      rw [hzero]
      simp only [deriv_zero, Pi.zero_apply, zero_add, Nat.succ_ne_zero, if_false]
      simp only [Nat.add_sub_cancel]
      rw [ih]
      push_cast
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- Derivative of a parameter Cauchy power under analytic motion of its pole. -/
theorem hasDerivAt_nevanlinnaCauchyPower
    {q : ℂ → ℂ} {z tau q' : ℂ} (hq : HasDerivAt q q' z)
    (hden : tau - q z ≠ 0) (k : ℕ) :
    HasDerivAt (fun w => ((tau - q w)⁻¹) ^ (k + 1))
      ((k + 1 : ℕ) * q' * ((tau - q z)⁻¹) ^ (k + 2)) z := by
  have hu : HasDerivAt (fun w => tau - q w) (-q') z := by
    have hsub := (hasDerivAt_const z tau).sub hq
    rw [show (fun w => tau - q w) = (fun _ => tau) - q by
      funext w
      rfl]
    apply hsub.congr_deriv
    ring
  have hinv := hu.inv hden
  have hpow := hinv.pow (k + 1)
  rw [show (fun w => ((tau - q w)⁻¹) ^ (k + 1)) =
      ((fun w => tau - q w)⁻¹) ^ (k + 1) by
    funext w
    rfl]
  apply hpow.congr_deriv
  simp [div_eq_mul_inv, pow_add, mul_assoc, mul_comm,
    mul_left_comm]

/-- Finite-sum reindexing used in the jet-expansion induction. -/
theorem nevanlinnaJet_sum_step
    (r : ℕ) (A B P : ℕ → ℂ) (q' : ℂ) (hA : A (r + 1) = 0) :
    (∑ k ∈ Finset.range (r + 1),
      (A k * P k + B k * ((k + 1 : ℕ) : ℂ) * q' * P (k + 1))) =
    ∑ k ∈ Finset.range (r + 2),
      (A k + if k = 0 then 0 else (k : ℂ) * q' * B (k - 1)) * P k := by
  have hAsum : (∑ k ∈ Finset.range (r + 2), A k * P k) =
      ∑ k ∈ Finset.range (r + 1), A k * P k := by
    rw [Finset.sum_range_succ, hA, zero_mul, add_zero]
  have hBsum :
      (∑ k ∈ Finset.range (r + 2),
        (if k = 0 then 0 else (k : ℂ) * q' * B (k - 1)) * P k) =
      ∑ k ∈ Finset.range (r + 1), B k * ↑(k + 1) * q' * P (k + 1) := by
    rw [Finset.sum_range_succ']
    simp only [if_pos, zero_mul, Nat.succ_ne_zero, if_false,
      Nat.add_sub_cancel]
    rw [add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    ring
  calc
    (∑ k ∈ Finset.range (r + 1),
        (A k * P k + B k * ↑(k + 1) * q' * P (k + 1))) =
      (∑ k ∈ Finset.range (r + 1), A k * P k) +
        ∑ k ∈ Finset.range (r + 1), B k * ↑(k + 1) * q' * P (k + 1) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ k ∈ Finset.range (r + 2), A k * P k) +
        ∑ k ∈ Finset.range (r + 2),
          (if k = 0 then 0 else (k : ℂ) * q' * B (k - 1)) * P k := by
          rw [hAsum, hBsum]
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- The finite Cauchy-power expansion of the `r`-th Nevanlinna jet. -/
noncomputable def nevanlinnaJetExpansion
    (a q : ℂ → ℂ) (tau : ℂ) (r : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (r + 1),
    nevanlinnaJetCoeff a q r k z * ((tau - q z)⁻¹) ^ (k + 1)

/-- Differentiating the order-`r` expansion gives the order-`r+1` expansion. -/
theorem hasDerivAt_nevanlinnaJetExpansion
    {a q : ℂ → ℂ} (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (tau z : ℂ) (hden : tau - q z ≠ 0) (r : ℕ) :
    HasDerivAt (nevanlinnaJetExpansion a q tau r)
      (nevanlinnaJetExpansion a q tau (r + 1) z) z := by
  have hqderiv : HasDerivAt q (deriv q z) z :=
    (hq.differentiable (by simp)).differentiableAt.hasDerivAt
  have hterm : ∀ k ∈ Finset.range (r + 1),
      HasDerivAt
        (fun w => nevanlinnaJetCoeff a q r k w *
          ((tau - q w)⁻¹) ^ (k + 1))
        (deriv (nevanlinnaJetCoeff a q r k) z * ((tau - q z)⁻¹) ^ (k + 1) +
          nevanlinnaJetCoeff a q r k z *
            ((k + 1 : ℕ) : ℂ) * deriv q z * ((tau - q z)⁻¹) ^ (k + 2)) z := by
    intro k hk
    have hb : HasDerivAt (nevanlinnaJetCoeff a q r k)
        (deriv (nevanlinnaJetCoeff a q r k) z) z :=
      ((contDiff_nevanlinnaJetCoeff ha hq r k).differentiable (by simp)).differentiableAt.hasDerivAt
    have hp := hasDerivAt_nevanlinnaCauchyPower hqderiv hden k
    have hmul := hb.mul hp
    rw [show
      (fun w => nevanlinnaJetCoeff a q r k w *
        ((tau - q w)⁻¹) ^ (k + 1)) =
      nevanlinnaJetCoeff a q r k *
        (fun w => ((tau - q w)⁻¹) ^ (k + 1)) by
      funext w
      rfl]
    apply hmul.congr_deriv
    ring
  have hsum := HasDerivAt.fun_sum hterm
  have hzero : deriv (nevanlinnaJetCoeff a q r (r + 1)) z = 0 := by
    rw [nevanlinnaJetCoeff_eq_zero_of_lt a q (Nat.lt_succ_self r), deriv_zero]
    rfl
  have hstep := nevanlinnaJet_sum_step r
    (fun k => deriv (nevanlinnaJetCoeff a q r k) z)
    (fun k => nevanlinnaJetCoeff a q r k z)
    (fun k => ((tau - q z)⁻¹) ^ (k + 1)) (deriv q z) hzero
  apply hsum.congr_deriv
  rw [hstep]
  simp only [nevanlinnaJetExpansion, nevanlinnaJetCoeff]

/-- Exact expansion of every genuine iterated Nevanlinna derivative in parameter Cauchy powers. -/
theorem iteratedDeriv_nevanlinnaKernel_eq_expansion
    {a q : ℂ → ℂ} (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (tau z : ℂ) (hden : tau - q z ≠ 0) : ∀ r,
    iteratedDeriv r (fun w => a w * (tau - q w)⁻¹) z =
      nevanlinnaJetExpansion a q tau r z := by
  intro r
  induction r generalizing z with
  | zero =>
      simp [nevanlinnaJetExpansion, nevanlinnaJetCoeff]
  | succ r ih =>
      rw [iteratedDeriv_succ]
      have hdenEv : ∀ᶠ w in 𝓝 z, tau - q w ≠ 0 :=
        ((continuous_const.sub hq.continuous).continuousAt.eventually_ne hden)
      have hlocal :
          iteratedDeriv r (fun w => a w * (tau - q w)⁻¹) =ᶠ[𝓝 z]
            nevanlinnaJetExpansion a q tau r := by
        filter_upwards [hdenEv] with w hw
        exact ih w hw
      rw [hlocal.deriv_eq]
      exact (hasDerivAt_nevanlinnaJetExpansion ha hq tau z hden r).deriv

/-- Finite lower-triangular matrix converting Cauchy powers into genuine jets at one node. -/
noncomputable def nevanlinnaJetMatrix
    (a q : ℂ → ℂ) (z : ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i k => if (k : ℕ) ≤ (i : ℕ) then nevanlinnaJetCoeff a q i k z else 0

/-- The finite jet-conversion matrix is lower triangular. -/
theorem nevanlinnaJetMatrix_lowerTriangular
    (a q : ℂ → ℂ) (z : ℂ) (n : ℕ) :
    (nevanlinnaJetMatrix a q z n).BlockTriangular
      (fun i : Fin n => OrderDual.toDual i) := by
  intro i k hik
  have hik' : (i : ℕ) < (k : ℕ) := OrderDual.toDual_lt_toDual.mp hik
  simp [nevanlinnaJetMatrix, Nat.not_le_of_lt hik']

/-- The matrix diagonal is the recursive coefficient diagonal. -/
@[simp] theorem nevanlinnaJetMatrix_diag
    (a q : ℂ → ℂ) (z : ℂ) (n : ℕ) (i : Fin n) :
    nevanlinnaJetMatrix a q z n i i = nevanlinnaJetCoeff a q i i z := by
  simp [nevanlinnaJetMatrix]

/-- Local nonvanishing of `a` and `q'` makes every finite conversion matrix invertible. -/
theorem nevanlinnaJetMatrix_det_ne_zero
    {a q : ℂ → ℂ} {z : ℂ} (ha : a z ≠ 0) (hq : deriv q z ≠ 0) (n : ℕ) :
    (nevanlinnaJetMatrix a q z n).det ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular _ (nevanlinnaJetMatrix_lowerTriangular a q z n)]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  rw [nevanlinnaJetMatrix_diag, nevanlinnaJetCoeff_diagonal]
  exact mul_ne_zero (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero i) ha)
    (pow_ne_zero _ hq)

/-- The one-node finite jet conversion as a complex-linear equivalence. -/
noncomputable def nevanlinnaJetLinearEquiv
    {a q : ℂ → ℂ} {z : ℂ} (ha : a z ≠ 0) (hq : deriv q z ≠ 0) (n : ℕ) :
    (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofBijective (nevanlinnaJetMatrix a q z n).mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det (nevanlinnaJetMatrix a q z n)).mpr
          (isUnit_iff_ne_zero.mpr (nevanlinnaJetMatrix_det_ne_zero ha hq n))),
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det (nevanlinnaJetMatrix a q z n)).mpr
          (isUnit_iff_ne_zero.mpr (nevanlinnaJetMatrix_det_ne_zero ha hq n)))⟩

/-- The one-node equivalence acts by the triangular conversion matrix. -/
@[simp] theorem nevanlinnaJetLinearEquiv_apply
    {a q : ℂ → ℂ} {z : ℂ} (ha : a z ≠ 0) (hq : deriv q z ≠ 0) (n : ℕ)
    (v : Fin n → ℂ) :
    nevanlinnaJetLinearEquiv ha hq n v =
      (nevanlinnaJetMatrix a q z n).mulVec v := rfl

/-- Expanding matrix-vector multiplication removes the explicit triangular guard. -/
theorem nevanlinnaJetMatrix_mulVec_apply
    (a q : ℂ → ℂ) (z : ℂ) (n : ℕ) (i : Fin n) (v : Fin n → ℂ) :
    (nevanlinnaJetMatrix a q z n).mulVec v i =
      ∑ k : Fin n, nevanlinnaJetCoeff a q i k z * v k := by
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hki : (k : ℕ) ≤ (i : ℕ)
  · simp [nevanlinnaJetMatrix, hki]
  · have hik : (i : ℕ) < (k : ℕ) := Nat.lt_of_not_ge hki
    rw [nevanlinnaJetCoeff_eq_zero_of_lt a q hik]
    simp [nevanlinnaJetMatrix, hki]

/-- The parameter Cauchy-power packet underlying the Nevanlinna jet at `z`. -/
def nevanlinnaCauchyPowerVector (q : ℂ → ℂ) (tau z : ℂ) (n : ℕ) : Fin n → ℂ :=
  fun k => ((tau - q z)⁻¹) ^ ((k : ℕ) + 1)

/-- A genuine one-node jet packet is exactly the triangular image of its Cauchy-power packet. -/
theorem nevanlinnaJetPacket_eq_linearEquiv_cauchyPower
    {a q : ℂ → ℂ} (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (tau z : ℂ) (hden : tau - q z ≠ 0)
    (haz : a z ≠ 0) (hqz : deriv q z ≠ 0) (n : ℕ) :
    (fun i : Fin n => iteratedDeriv i (fun w => a w * (tau - q w)⁻¹) z) =
      nevanlinnaJetLinearEquiv haz hqz n (nevanlinnaCauchyPowerVector q tau z n) := by
  funext i
  rw [iteratedDeriv_nevanlinnaKernel_eq_expansion ha hq tau z hden i]
  rw [nevanlinnaJetLinearEquiv_apply, nevanlinnaJetMatrix_mulVec_apply]
  simp only [nevanlinnaJetExpansion, nevanlinnaCauchyPowerVector]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => nevanlinnaJetCoeff a q (i : ℕ) k z *
      ((tau - q z)⁻¹) ^ (k + 1)) n]
  apply Finset.sum_subset
  · intro k hk
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hk) i.isLt)
  · intro k hkn hknot
    have hik : (i : ℕ) < k := by
      exact Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hknot)
    rw [nevanlinnaJetCoeff_eq_zero_of_lt a q hik]
    simp

/-- The product of the invertible triangular jet changes of coordinates at finitely many nodes. -/
def nevanlinnaJetPacketLinearEquiv
    {ι : Type*} (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0) :
    ((Σ i, Fin (n i)) → ℂ) ≃ₗ[ℂ] ((Σ i, Fin (n i)) → ℂ) where
  toFun v s :=
    nevanlinnaJetLinearEquiv (ha s.1) (hq s.1) (n s.1)
      (fun k => v ⟨s.1, k⟩) s.2
  invFun v s :=
    (nevanlinnaJetLinearEquiv (ha s.1) (hq s.1) (n s.1)).symm
      (fun k => v ⟨s.1, k⟩) s.2
  left_inv v := by
    funext s
    have h := (nevanlinnaJetLinearEquiv (ha s.1) (hq s.1) (n s.1)).symm_apply_apply
      (fun k => v ⟨s.1, k⟩)
    exact congrFun h s.2
  right_inv v := by
    funext s
    have h := (nevanlinnaJetLinearEquiv (ha s.1) (hq s.1) (n s.1)).apply_symm_apply
      (fun k => v ⟨s.1, k⟩)
    exact congrFun h s.2
  map_add' v w := by
    funext s
    change
      nevanlinnaJetLinearEquiv (ha s.1) (hq s.1) (n s.1)
          (fun k => v ⟨s.1, k⟩ + w ⟨s.1, k⟩) s.2 =
        nevanlinnaJetLinearEquiv (ha s.1) (hq s.1) (n s.1)
            (fun k => v ⟨s.1, k⟩) s.2 +
          nevanlinnaJetLinearEquiv (ha s.1) (hq s.1) (n s.1)
            (fun k => w ⟨s.1, k⟩) s.2
    have hinput :
        (fun k => v ⟨s.1, k⟩ + w ⟨s.1, k⟩) =
          (fun k => v ⟨s.1, k⟩) + (fun k => w ⟨s.1, k⟩) := by
      funext k
      rfl
    rw [hinput]
    exact congrFun
      (map_add (nevanlinnaJetLinearEquiv (ha s.1) (hq s.1) (n s.1))
        (fun k => v ⟨s.1, k⟩) (fun k => w ⟨s.1, k⟩)) s.2
  map_smul' c v := by
    funext s
    change
      nevanlinnaJetLinearEquiv (ha s.1) (hq s.1) (n s.1)
          (fun k => c • v ⟨s.1, k⟩) s.2 =
        (RingHom.id ℂ) c •
          nevanlinnaJetLinearEquiv (ha s.1) (hq s.1) (n s.1)
            (fun k => v ⟨s.1, k⟩) s.2
    have hinput :
        (fun k => c • v ⟨s.1, k⟩) =
          c • (fun k => v ⟨s.1, k⟩) := by
      funext k
      rfl
    rw [hinput]
    exact congrFun
      (map_smul (nevanlinnaJetLinearEquiv (ha s.1) (hq s.1) (n s.1)) c
        (fun k => v ⟨s.1, k⟩)) s.2

/-- Coordinate formula for the finite product jet equivalence. -/
@[simp] theorem nevanlinnaJetPacketLinearEquiv_apply
    {ι : Type*} (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0)
    (v : (Σ i, Fin (n i)) → ℂ) (s : Σ i, Fin (n i)) :
    nevanlinnaJetPacketLinearEquiv a q z n ha hq v s =
      nevanlinnaJetLinearEquiv (ha s.1) (hq s.1) (n s.1)
        (fun k => v ⟨s.1, k⟩) s.2 := rfl

/-- Simultaneous genuine jets at arbitrary finitely indexed nodes equal the product triangular
image of their parameter Cauchy powers. -/
theorem nevanlinnaJetPacket_eq_packetLinearEquiv
    {ι : Type*} {a q : ℂ → ℂ} (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (z : ι → ℂ) (n : ι → ℕ) (tau : ℂ)
    (hden : ∀ i, tau - q (z i) ≠ 0)
    (haz : ∀ i, a (z i) ≠ 0) (hqz : ∀ i, deriv q (z i) ≠ 0) :
    (fun s : Σ i, Fin (n i) =>
      iteratedDeriv s.2 (fun w => a w * (tau - q w)⁻¹) (z s.1)) =
      nevanlinnaJetPacketLinearEquiv a q z n haz hqz
        (fun s => ((tau - q (z s.1))⁻¹) ^ ((s.2 : ℕ) + 1)) := by
  funext s
  have h := nevanlinnaJetPacket_eq_linearEquiv_cauchyPower
    ha hq tau (z s.1) (hden s.1) (haz s.1) (hqz s.1) (n s.1)
  exact congrFun h s.2

/-- The finite-support control map for genuine Nevanlinna `z`-jets. -/
def nevanlinnaJetRealLinearCombination
    {ι κ : Type*} (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0) (t : κ → ℝ) :
    (κ →₀ ℝ) →ₗ[ℝ] ((Σ i, Fin (n i)) → ℂ) :=
  (nevanlinnaJetPacketLinearEquiv a q z n ha hq).restrictScalars ℝ |>.toLinearMap.comp
    (cauchyJetRealLinearCombination (fun i => q (z i)) n t)

/-- A single real parameter mass is sent to its genuine finite Nevanlinna-jet packet. -/
theorem nevanlinnaJetRealLinearCombination_single
    {ι κ : Type*} {a q : ℂ → ℂ} (ha : ContDiff ℂ ⊤ a) (hq : ContDiff ℂ ⊤ q)
    (z : ι → ℂ) (n : ι → ℕ)
    (haz : ∀ i, a (z i) ≠ 0) (hqz : ∀ i, deriv q (z i) ≠ 0)
    (t : κ → ℝ) (p : κ) (hden : ∀ i, (t p : ℂ) - q (z i) ≠ 0) :
    nevanlinnaJetRealLinearCombination a q z n haz hqz t (Finsupp.single p 1) =
      fun s : Σ i, Fin (n i) =>
        iteratedDeriv s.2 (fun w => a w * ((t p : ℂ) - q w)⁻¹) (z s.1) := by
  rw [nevanlinnaJetRealLinearCombination, LinearMap.comp_apply]
  have hcolumn :
      cauchyJetRealLinearCombination (fun i => q (z i)) n t (Finsupp.single p 1) =
        fun s : Σ i, Fin (n i) =>
          (((t p : ℂ) - q (z s.1))⁻¹) ^ ((s.2 : ℕ) + 1) := by
    rw [show cauchyJetRealLinearCombination (fun i => q (z i)) n t
        (Finsupp.single p 1) =
          cauchyJetColumn (fun i => q (z i)) n (fun p => (t p : ℂ)) p by
      simp [cauchyJetRealLinearCombination]]
    rfl
  rw [hcolumn]
  exact (nevanlinnaJetPacket_eq_packetLinearEquiv
    ha hq z n (t p : ℂ) hden haz hqz).symm

/-- Genuine Nevanlinna jet control remains onto after an exact disjoint genuine jet packet is
frozen.  This is the analytic triangular upgrade of constrained Cauchy-jet controllability. -/
theorem constrainedNevanlinnaJetRealLinearCombination_surjective
    {ιf ιt κ : Type*} [Fintype ιf] [DecidableEq ιf]
    [Fintype ιt] [DecidableEq ιt] [Infinite κ]
    (a q : ℂ → ℂ)
    (zf : ιf → ℂ) (zt : ιt → ℂ)
    (hqf_inj : Function.Injective (fun i => q (zf i)))
    (hqt_inj : Function.Injective (fun i => q (zt i)))
    (hcross : ∀ i j, q (zf i) ≠ q (zt j))
    (hupperf : ∀ i, 0 < (q (zf i)).im) (huppert : ∀ i, 0 < (q (zt i)).im)
    (nf : ιf → ℕ) (nt : ιt → ℕ)
    (haf : ∀ i, a (zf i) ≠ 0) (hat : ∀ i, a (zt i) ≠ 0)
    (hqdf : ∀ i, deriv q (zf i) ≠ 0) (hqdt : ∀ i, deriv q (zt i) ≠ 0)
    (t : κ → ℝ) (ht : Function.Injective t) :
    Function.Surjective
      ((nevanlinnaJetRealLinearCombination a q zt nt hat hqdt t).domRestrict
        (LinearMap.ker (nevanlinnaJetRealLinearCombination a q zf nf haf hqdf t))) := by
  exact constrainedControl_surjective_of_linearEquiv
    (cauchyJetRealLinearCombination (fun i => q (zf i)) nf t)
    (cauchyJetRealLinearCombination (fun i => q (zt i)) nt t)
    ((nevanlinnaJetPacketLinearEquiv a q zf nf haf hqdf).restrictScalars ℝ)
    ((nevanlinnaJetPacketLinearEquiv a q zt nt hat hqdt).restrictScalars ℝ)
    (constrainedCauchyJetRealLinearCombination_surjective
      (fun i => q (zf i)) hqf_inj (fun i => q (zt i)) hqt_inj hcross
      hupperf huppert nf nt t ht)

end
end GaloisForLFunctions.HTGeometry
