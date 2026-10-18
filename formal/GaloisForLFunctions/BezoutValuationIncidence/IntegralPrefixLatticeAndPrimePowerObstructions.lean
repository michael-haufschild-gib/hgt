import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.QuotientRing
import GaloisForLFunctions.BezoutValuationIncidence.SharpInitialPrefixObservabilityAndExactGramDeterminants
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.SimpleHorizonTransmutation

/-!
# Integral prefix lattices and prime-power obstructions

The actual Ramanujan primitive matrix on prefix lengths `1,...,n` and moduli
`2,...,n+1` has an explicit integral equivalence to `diag(1,...,n)`. The row
and column transforms are unimodular, including at dimension zero. The proof
uses ordered floor responses, a terminal-column shear, and divisor incidence.

This gives all congruence obstructions to integral interpolation, a canonical
reconstruction, and the cokernel `∏ k : Fin n, ZMod (k+1)`. Base change gives
exact modular kernels: at a prime power `p^a` their cardinality is
`p^(Σ_{r=1}^a floor(n/p^r))`, and the rank modulo `p` is `n-floor(n/p)`.

The integral lattice consists of integer Ramanujan amplitudes, equivalently
integer normalized weights `c(d)/d`. It does not require arbitrary integer raw
weights to have integer normalized coordinates. No analytic cancellation or
uniform conditioning estimate is asserted.
-/

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
open Finset
open scoped BigOperators Matrix

/-- Integral floor responses on the first positive integers. -/
def sievePrefixIntegerFloorMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (((i.val + 1) / (j.val + 1) : ℕ) : ℤ)

/-- Centered prefix responses to weights divisible by their divisor index. -/
def sievePrefixScaledIntegerObservationMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => ((j.val + 2 : ℕ) : ℤ) * (((i.val + 1) / (j.val + 2) : ℕ) : ℤ) -
    ((i.val + 1 : ℕ) : ℤ)

/-- The integral divisor-incidence change from normalized weights to amplitudes. -/
def sievePrefixDivisorIncidenceMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i.val + 2 ∣ j.val + 2 then 1 else 0

theorem sievePrefixIntegerFloorMatrix_det (n : ℕ) :
    (sievePrefixIntegerFloorMatrix n).det = 1 := by
  have htri : (sievePrefixIntegerFloorMatrix n).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i.val < j.val := hij
    change (((i.val + 1) / (j.val + 1) : ℕ) : ℤ) = 0
    rw [Nat.div_eq_of_lt (by omega), Nat.cast_zero]
  rw [Matrix.det_of_lowerTriangular _ htri]
  simp [sievePrefixIntegerFloorMatrix]

theorem sievePrefixDivisorIncidenceMatrix_det (n : ℕ) :
    (sievePrefixDivisorIncidenceMatrix n).det = 1 := by
  have htri : (sievePrefixDivisorIncidenceMatrix n).BlockTriangular id := by
    intro i j hij
    have hlt : j.val < i.val := hij
    have hnot : ¬ i.val + 2 ∣ j.val + 2 := by
      intro h
      have := Nat.le_of_dvd (by omega : 0 < j.val + 2) h
      omega
    simp [sievePrefixDivisorIncidenceMatrix, hnot]
  rw [Matrix.det_of_upperTriangular htri]
  simp [sievePrefixDivisorIncidenceMatrix]

private def prefixIntegralShear (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => (if i = j then 1 else 0) +
    (if j = Fin.last n then 0 else if i = Fin.last n then -1 else 0)

private theorem prefixIntegralShear_det (n : ℕ) : (prefixIntegralShear n).det = 1 := by
  have htri : (prefixIntegralShear n).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i.val < j.val := hij
    have hij' : i ≠ j := by intro h; subst j; omega
    have hi : i ≠ Fin.last n := by intro h; subst i; simp only [Fin.val_last] at hlt; omega
    simp [prefixIntegralShear, hij', hi]
  have hdiag (i : Fin (n + 1)) : prefixIntegralShear n i i = 1 := by
    by_cases hi : i = Fin.last n <;> simp [prefixIntegralShear, hi]
  rw [Matrix.det_of_lowerTriangular _ htri]
  simp_rw [hdiag]
  simp

private theorem prefixIntegralShear_mul (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (i j : Fin (n + 1)) :
    (M * prefixIntegralShear n) i j =
      M i j + if j = Fin.last n then 0 else -M i (Fin.last n) := by
  classical
  by_cases hj : j = Fin.last n <;>
    simp [Matrix.mul_apply, prefixIntegralShear, mul_add, mul_ite,
      Finset.sum_add_distrib, hj]

private def prefixIntegralRotation (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => if i = finRotate (n + 1) j then (if j = Fin.last n then -1 else 1) else 0

private theorem prefixIntegralRotation_det (n : ℕ) :
    (prefixIntegralRotation n).det = (-1 : ℤ) ^ (n + 1) := by
  have hq : (∏ j : Fin (n + 1), if j = Fin.last n then (-1 : ℤ) else 1) = -1 := by
    rw [Fin.prod_univ_castSucc]
    simp
  have he : prefixIntegralRotation n =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).submatrix id (finRotate (n + 1)) *
        Matrix.diagonal (fun j => if j = Fin.last n then -1 else 1) := by
    ext i j
    simp only [prefixIntegralRotation, Matrix.mul_diagonal,
      Matrix.submatrix_apply, Matrix.one_apply, id_eq]
    split_ifs <;> simp
  rw [he, Matrix.det_mul, Matrix.det_diagonal, hq]
  simp [Matrix.det_permute', sign_finRotate, pow_succ]

private theorem prefixIntegralRotation_unit (n : ℕ) :
    IsUnit (prefixIntegralRotation n).det := by
  rw [prefixIntegralRotation_det]
  exact (isUnit_one.neg).pow _

private theorem prefixIntegralRotation_mul (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (i j : Fin (n + 1)) :
    (M * prefixIntegralRotation n) i j =
      M i (finRotate (n + 1) j) * (if j = Fin.last n then -1 else 1) := by
  classical
  simp [Matrix.mul_apply, prefixIntegralRotation, mul_ite]

private theorem prefixIntegralScaled_shear (n : ℕ) :
    sievePrefixScaledIntegerObservationMatrix (n + 1) * prefixIntegralShear n =
      sievePrefixIntegerFloorMatrix (n + 1) *
        Matrix.diagonal (fun i : Fin (n + 1) => ((i.val + 1 : ℕ) : ℤ)) *
          prefixIntegralRotation n := by
  have hlast (i : Fin (n + 1)) :
      sievePrefixScaledIntegerObservationMatrix (n + 1) i (Fin.last n) =
        -((i.val + 1 : ℕ) : ℤ) := by
    have hdiv : (i.val + 1) / (n + 2) = 0 := Nat.div_eq_of_lt (by omega)
    simp [sievePrefixScaledIntegerObservationMatrix, hdiv]
  ext i j
  rw [prefixIntegralShear_mul, prefixIntegralRotation_mul, Matrix.mul_diagonal, hlast]
  by_cases hj : j = Fin.last n
  · subst j
    rw [hlast]
    simp [sievePrefixIntegerFloorMatrix]
  · simp only [hj, if_false, coe_finRotate_of_ne_last hj,
      sievePrefixIntegerFloorMatrix, sievePrefixScaledIntegerObservationMatrix]
    have he : j.val + 1 + 1 = j.val + 2 := by omega
    rw [he]
    ring

/-- Integral column operations exposing the consecutive diagonal of floor observations. -/
def sievePrefixIntegerObservationReducer : (n : ℕ) → Matrix (Fin n) (Fin n) ℤ
  | 0 => 1
  | n + 1 => prefixIntegralShear n * (prefixIntegralRotation n)⁻¹

theorem sievePrefixIntegerObservationReducer_unit (n : ℕ) :
    IsUnit (sievePrefixIntegerObservationReducer n).det := by
  cases n with
  | zero => simp [sievePrefixIntegerObservationReducer]
  | succ n =>
    rw [sievePrefixIntegerObservationReducer, Matrix.det_mul, prefixIntegralShear_det, one_mul]
    exact Matrix.isUnit_nonsing_inv_det _ (prefixIntegralRotation_unit n)

theorem sievePrefixScaledIntegerObservationMatrix_reduction (n : ℕ) :
    sievePrefixScaledIntegerObservationMatrix n * sievePrefixIntegerObservationReducer n =
      sievePrefixIntegerFloorMatrix n *
        Matrix.diagonal (fun i : Fin n => ((i.val + 1 : ℕ) : ℤ)) := by
  cases n with
  | zero => ext i; exact Fin.elim0 i
  | succ n =>
    rw [sievePrefixIntegerObservationReducer, ← Matrix.mul_assoc, prefixIntegralScaled_shear,
      Matrix.mul_nonsing_inv_cancel_right _ _ (prefixIntegralRotation_unit n)]


private theorem prefix_card_fin_multiples (n d : ℕ) :
    Fintype.card {i : Fin n // d ∣ i.val + 1} = n / d := by
  classical
  calc
    _ = ∑ i : Fin n, if d ∣ i.val + 1 then 1 else 0 := by
      rw [Fintype.card_subtype, Finset.card_filter]
    _ = ∑ k ∈ Finset.range n, if d ∣ k + 1 then 1 else 0 :=
      Fin.sum_univ_eq_sum_range (fun k => if d ∣ k + 1 then 1 else 0) n
    _ = n / d := by simpa only [Finset.card_filter] using Nat.card_multiples n d

private theorem prefix_scalar_kernel_card (m k : ℕ) [NeZero m] :
    Nat.card {x : ZMod m // (k : ZMod m) * x = 0} = Nat.gcd m k := by
  let e : {x : ZMod m // (k : ZMod m) * x = 0} ≃
      (nsmulAddMonoidHom k : ZMod m →+ ZMod m).ker :=
    { toFun := fun x => ⟨x.val, by
        change k • x.val = 0
        simpa only [nsmul_eq_mul] using x.property⟩
      invFun := fun x => ⟨x.val, by
        have hx : k • x.val = 0 := x.property
        simpa only [nsmul_eq_mul] using hx⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simpa only [Nat.card_zmod] using
    IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) k

private theorem prefix_gcd_prime_power_step (p : Nat.Primes) (a k : ℕ) :
    Nat.gcd ((p : ℕ) ^ (a + 1)) k =
      (if (p : ℕ) ^ (a + 1) ∣ k then (p : ℕ) else 1) *
        Nat.gcd ((p : ℕ) ^ a) k := by
  by_cases h : (p : ℕ) ^ (a + 1) ∣ k
  · have ha : (p : ℕ) ^ a ∣ k :=
      (Nat.pow_dvd_pow (p : ℕ) (by omega : a ≤ a + 1)).trans h
    rw [if_pos h, Nat.gcd_eq_left_iff_dvd.mpr h, Nat.gcd_eq_left_iff_dvd.mpr ha,
      pow_succ]
    exact Nat.mul_comm _ _
  · rw [if_neg h, one_mul]
    apply Nat.dvd_antisymm
    · apply Nat.dvd_gcd
      · obtain ⟨r, hr, he⟩ := (Nat.dvd_prime_pow p.property).mp
          (Nat.gcd_dvd_left ((p : ℕ) ^ (a + 1)) k)
        have hra : r ≤ a := by
          by_contra hn
          have heq : r = a + 1 := by omega
          apply h
          rw [← heq, ← he]
          exact Nat.gcd_dvd_right _ _
        rw [he]
        exact Nat.pow_dvd_pow (p : ℕ) hra
      · exact Nat.gcd_dvd_right _ _
    · exact Nat.dvd_gcd
        ((Nat.gcd_dvd_left ((p : ℕ) ^ a) k).trans
          (Nat.pow_dvd_pow (p : ℕ) (by omega : a ≤ a + 1)))
        (Nat.gcd_dvd_right _ _)

private theorem prefix_gcd_product_step (n : ℕ) (p : Nat.Primes) (a : ℕ) :
    (∏ i : Fin n, Nat.gcd ((p : ℕ) ^ (a + 1)) (i.val + 1)) =
      (p : ℕ) ^ (n / (p : ℕ) ^ (a + 1)) *
        (∏ i : Fin n, Nat.gcd ((p : ℕ) ^ a) (i.val + 1)) := by
  classical
  simp_rw [prefix_gcd_prime_power_step]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_filter, Finset.prod_const]
  congr 1
  simpa only [Fintype.card_subtype] using prefix_card_fin_multiples n ((p : ℕ) ^ (a + 1))

private theorem prefix_gcd_product_prime_power (n : ℕ) (p : Nat.Primes) (a : ℕ) :
    (∏ i : Fin n, Nat.gcd ((p : ℕ) ^ a) (i.val + 1)) =
      (p : ℕ) ^ (∑ r ∈ Finset.range a, n / (p : ℕ) ^ (r + 1)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [prefix_gcd_product_step, ih, ← pow_add, Finset.sum_range_succ]
    congr 1
    omega

private theorem prefix_diagonal_prime_rank (n : ℕ) (p : Nat.Primes) :
    (Matrix.diagonal (fun i : Fin n => ((i.val + 1 : ℕ) : ZMod (p : ℕ)))).rank =
      n - n / (p : ℕ) := by
  classical
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  rw [Matrix.rank_diagonal, Fintype.card_subtype_compl, Fintype.card_fin]
  congr 1
  simpa only [ZMod.natCast_eq_zero_iff] using prefix_card_fin_multiples n (p : ℕ)

private def prefix_kernel_diagonal_equiv {K : Type*} [CommRing K] {n : ℕ}
    (M U V : Matrix (Fin n) (Fin n) K) (d : Fin n → K)
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (h : U * M * V = Matrix.diagonal d) :
    {x : Fin n → K // M *ᵥ x = 0} ≃ ∀ i : Fin n, {x : K // d i * x = 0} := by
  classical
  have hUinj := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det U).mpr hU)
  have hDV : Matrix.diagonal d * V⁻¹ = U * M := by
    rw [← h, Matrix.mul_nonsing_inv_cancel_right _ _ hV]
  have happly (x : Fin n → K) : U *ᵥ (M *ᵥ (V *ᵥ x)) = Matrix.diagonal d *ᵥ x := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  refine
    { toFun := fun x i => ⟨(V⁻¹ *ᵥ x.val) i, ?_⟩
      invFun := fun x => ⟨V *ᵥ (fun i => (x i).val), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have he : Matrix.diagonal d *ᵥ (V⁻¹ *ᵥ x.val) = 0 := by
      rw [Matrix.mulVec_mulVec, hDV, ← Matrix.mulVec_mulVec, x.property,
        Matrix.mulVec_zero]
    simpa [Matrix.mulVec_diagonal] using congrFun he i
  · apply hUinj
    rw [happly, Matrix.mulVec_zero]
    ext i
    simpa [Matrix.mulVec_diagonal] using (x i).property
  · intro x
    apply Subtype.ext
    change V *ᵥ (V⁻¹ *ᵥ x.val) = x.val
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hV, Matrix.one_mulVec]
  · intro x
    funext i
    apply Subtype.ext
    change (V⁻¹ *ᵥ (V *ᵥ fun j => (x j).val)) i = (x i).val
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hV, Matrix.one_mulVec]

private theorem prefix_solvable_iff {K : Type*} [CommRing K] {n : ℕ}
    (M U V : Matrix (Fin n) (Fin n) K) (d : Fin n → K)
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (h : U * M * V = Matrix.diagonal d) (y : Fin n → K) :
    (∃ x : Fin n → K, M *ᵥ x = y) ↔ ∀ i, d i ∣ (U *ᵥ y) i := by
  classical
  have hUinj := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det U).mpr hU)
  have hDV : Matrix.diagonal d * V⁻¹ = U * M := by
    rw [← h, Matrix.mul_nonsing_inv_cancel_right _ _ hV]
  constructor
  · rintro ⟨x, hx⟩ i
    refine ⟨(V⁻¹ *ᵥ x) i, ?_⟩
    have he : Matrix.diagonal d *ᵥ (V⁻¹ *ᵥ x) = U *ᵥ y := by
      rw [Matrix.mulVec_mulVec, hDV, ← Matrix.mulVec_mulVec, hx]
    simpa [Matrix.mulVec_diagonal] using congrFun he.symm i
  · intro hy
    choose x hx using hy
    refine ⟨V *ᵥ x, hUinj ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
    ext i
    simpa [Matrix.mulVec_diagonal] using (hx i).symm

private theorem prefix_integral_matrix_injective {n : ℕ}
    (M U V : Matrix (Fin n) (Fin n) ℤ)
    (hV : IsUnit V.det)
    (h : U * M * V = Matrix.diagonal (fun i : Fin n => ((i.val + 1 : ℕ) : ℤ))) :
    Function.Injective M.mulVec := by
  have hDV : Matrix.diagonal (fun i : Fin n => ((i.val + 1 : ℕ) : ℤ)) * V⁻¹ = U * M := by
    rw [← h, Matrix.mul_nonsing_inv_cancel_right _ _ hV]
  intro x y hxy
  have he : Matrix.diagonal (fun i : Fin n => ((i.val + 1 : ℕ) : ℤ)) *ᵥ (V⁻¹ *ᵥ x) =
      Matrix.diagonal (fun i : Fin n => ((i.val + 1 : ℕ) : ℤ)) *ᵥ (V⁻¹ *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hDV, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hxy]
  have hv : V⁻¹ *ᵥ x = V⁻¹ *ᵥ y := by
    ext i
    have hi := congrFun he i
    have hk : ((i.val + 1 : ℕ) : ℤ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hk
    simpa [Matrix.mulVec_diagonal] using hi
  exact Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det V hV)) hv

private theorem prefix_map_det_unit {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) (h : IsUnit M.det) :
    IsUnit (M.map (Int.castRingHom K)).det := by
  change IsUnit ((Int.castRingHom K).mapMatrix M).det
  rw [← RingHom.map_det]
  exact h.map (Int.castRingHom K)

private theorem prefix_map_diagonal_int (K : Type*) [CommRing K] (n : ℕ) :
    (Matrix.diagonal (fun i : Fin n => ((i.val + 1 : ℕ) : ℤ))).map (Int.castRingHom K) =
      Matrix.diagonal (fun i : Fin n => ((i.val + 1 : ℕ) : K)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

open ArithmeticFunction _root_.RHTower

/-- The integer-valued primitive underlying the complex Ramanujan prefix. -/
def sieveIntegralRamanujanPrimitive (q N : ℕ) : ℤ :=
  ∑ x ∈ q.divisorsAntidiagonal,
    (x.1 : ℤ) * moebius x.2 * ((N / x.1 : ℕ) : ℤ)

theorem sieveIntegralRamanujanPrimitive_complex (q N : ℕ) :
    (sieveIntegralRamanujanPrimitive q N : ℂ) = pmRamanujanPrimitive q N := by
  simp only [sieveIntegralRamanujanPrimitive, pmRamanujanPrimitive_eq_floor,
    Int.cast_sum, Int.cast_mul, Int.cast_natCast]

theorem sieveIntegralRamanujanPrimitive_real (q N : ℕ) :
    (sieveIntegralRamanujanPrimitive q N : ℝ) = (pmRamanujanPrimitive q N).re := by
  simpa only [Complex.intCast_re] using
    congrArg Complex.re (sieveIntegralRamanujanPrimitive_complex q N)

/-- Actual Ramanujan prefixes, with their integral values retained. -/
def sievePrefixIntegralRamanujanMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => sieveIntegralRamanujanPrimitive (j.val + 2) (i.val + 1)

theorem sievePrefixIntegralRamanujanMatrix_real (n : ℕ) :
    (sievePrefixIntegralRamanujanMatrix n).map (Int.castRingHom ℝ) =
      sievePrefixRamanujanMatrix n := by
  ext i j
  exact sieveIntegralRamanujanPrimitive_real (j.val + 2) (i.val + 1)

theorem sievePrefixScaledIntegerObservationMatrix_real (n : ℕ) :
    (sievePrefixScaledIntegerObservationMatrix n).map (Int.castRingHom ℝ) =
      sievePrefixObservationMatrix n *
        Matrix.diagonal (fun j : Fin n => ((j.val + 2 : ℕ) : ℝ)) := by
  ext i j
  rw [Matrix.mul_diagonal]
  change ((((j.val + 2 : ℕ) : ℤ) * (((i.val + 1) / (j.val + 2) : ℕ) : ℤ) -
      ((i.val + 1 : ℕ) : ℤ) : ℤ) : ℝ) =
    ((((i.val + 1) / (j.val + 2) : ℕ) : ℝ) -
      ((i.val + 1 : ℕ) : ℝ) / ((j.val + 2 : ℕ) : ℝ)) * ((j.val + 2 : ℕ) : ℝ)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  rw [sub_mul, div_mul_cancel₀ _ (by positivity)]
  ring

private theorem prefix_incidence_real (n : ℕ) :
    (sievePrefixDivisorIncidenceMatrix n).map (Int.castRingHom ℝ) =
      sieveTailMultiplesMatrix n *
        Matrix.diagonal (fun j : Fin n => ((j.val + 2 : ℕ) : ℝ)) := by
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [Matrix.map_apply, sievePrefixDivisorIncidenceMatrix, sieveTailMultiplesMatrix]
  split_ifs <;> simp [show (j.val : ℝ) + 2 ≠ 0 by positivity]

/-- Integral incidence factorization of the actual primitive matrix. -/
theorem sievePrefixIntegralRamanujanMatrix_incidence (n : ℕ) :
    sievePrefixIntegralRamanujanMatrix n * sievePrefixDivisorIncidenceMatrix n =
      sievePrefixScaledIntegerObservationMatrix n := by
  have h : (sievePrefixIntegralRamanujanMatrix n * sievePrefixDivisorIncidenceMatrix n).map
      (Int.castRingHom ℝ) =
        (sievePrefixScaledIntegerObservationMatrix n).map (Int.castRingHom ℝ) := by
    rw [Matrix.map_mul, sievePrefixIntegralRamanujanMatrix_real, prefix_incidence_real,
      ← Matrix.mul_assoc, ← sievePrefixObservationMatrix_factorization,
      sievePrefixScaledIntegerObservationMatrix_real]
  ext i j
  apply Int.cast_injective (α := ℝ)
  exact congrArg (fun M => M i j) h

/-- Integral row coordinates in which the interpolation congruences separate. -/
def sievePrefixIntegralLeftTransform (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  (sievePrefixIntegerFloorMatrix n)⁻¹

/-- Integral amplitude coordinates reducing the prefix lattice to consecutive moduli. -/
def sievePrefixIntegralRightTransform (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  sievePrefixDivisorIncidenceMatrix n * sievePrefixIntegerObservationReducer n

theorem sievePrefixIntegralLeftTransform_unit (n : ℕ) :
    IsUnit (sievePrefixIntegralLeftTransform n).det := by
  apply Matrix.isUnit_nonsing_inv_det
  rw [sievePrefixIntegerFloorMatrix_det]
  exact isUnit_one

theorem sievePrefixIntegralRightTransform_unit (n : ℕ) :
    IsUnit (sievePrefixIntegralRightTransform n).det := by
  rw [sievePrefixIntegralRightTransform, Matrix.det_mul,
    sievePrefixDivisorIncidenceMatrix_det, one_mul]
  exact sievePrefixIntegerObservationReducer_unit n

/-- Explicit unimodular reduction to `diag(1,...,n)` at every dimension. -/
theorem sievePrefixIntegralRamanujanMatrix_reduction (n : ℕ) :
    sievePrefixIntegralLeftTransform n * sievePrefixIntegralRamanujanMatrix n *
      sievePrefixIntegralRightTransform n =
        Matrix.diagonal (fun i : Fin n => ((i.val + 1 : ℕ) : ℤ)) := by
  have hF : IsUnit (sievePrefixIntegerFloorMatrix n).det := by
    rw [sievePrefixIntegerFloorMatrix_det]
    exact isUnit_one
  change (sievePrefixIntegerFloorMatrix n)⁻¹ * sievePrefixIntegralRamanujanMatrix n *
    (sievePrefixDivisorIncidenceMatrix n * sievePrefixIntegerObservationReducer n) = _
  calc
    _ = (sievePrefixIntegerFloorMatrix n)⁻¹ *
        ((sievePrefixIntegralRamanujanMatrix n * sievePrefixDivisorIncidenceMatrix n) *
          sievePrefixIntegerObservationReducer n) := by simp only [Matrix.mul_assoc]
    _ = (sievePrefixIntegerFloorMatrix n)⁻¹ *
        (sievePrefixIntegerFloorMatrix n *
          Matrix.diagonal (fun i : Fin n => ((i.val + 1 : ℕ) : ℤ))) := by
      rw [sievePrefixIntegralRamanujanMatrix_incidence,
        sievePrefixScaledIntegerObservationMatrix_reduction]
    _ = _ := Matrix.nonsing_inv_mul_cancel_left _ _ hF

/-- Reduction of the actual integral prefix operator over an arbitrary coefficient ring. -/
def sievePrefixIntegralMatrixOver (n : ℕ) (K : Type*) [CommRing K] :
    Matrix (Fin n) (Fin n) K :=
  (sievePrefixIntegralRamanujanMatrix n).map (Int.castRingHom K)

theorem sievePrefixIntegralMatrixOver_reduction (n : ℕ) (K : Type*) [CommRing K] :
    (sievePrefixIntegralLeftTransform n).map (Int.castRingHom K) *
      sievePrefixIntegralMatrixOver n K *
      (sievePrefixIntegralRightTransform n).map (Int.castRingHom K) =
        Matrix.diagonal (fun i : Fin n => ((i.val + 1 : ℕ) : K)) := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M.map (Int.castRingHom K))
    (sievePrefixIntegralRamanujanMatrix_reduction n)
  simpa only [Matrix.map_mul, prefix_map_diagonal_int, sievePrefixIntegralMatrixOver] using h

/-- Every integral interpolation obstruction is one of these separated congruences. -/
theorem sievePrefixIntegral_solvable_iff (n : ℕ) (y : Fin n → ℤ) :
    (∃ x : Fin n → ℤ, sievePrefixIntegralRamanujanMatrix n *ᵥ x = y) ↔
      ∀ i : Fin n, ((i.val + 1 : ℕ) : ℤ) ∣ (sievePrefixIntegralLeftTransform n *ᵥ y) i :=
  prefix_solvable_iff _ _ _ _ (sievePrefixIntegralLeftTransform_unit n)
    (sievePrefixIntegralRightTransform_unit n) (sievePrefixIntegralRamanujanMatrix_reduction n) y

theorem sievePrefixIntegral_injective (n : ℕ) :
    Function.Injective (sievePrefixIntegralRamanujanMatrix n).mulVec :=
  prefix_integral_matrix_injective _ _ _ (sievePrefixIntegralRightTransform_unit n)
    (sievePrefixIntegralRamanujanMatrix_reduction n)

theorem sievePrefixIntegral_existsUnique_iff (n : ℕ) (y : Fin n → ℤ) :
    (∃! x : Fin n → ℤ, sievePrefixIntegralRamanujanMatrix n *ᵥ x = y) ↔
      ∀ i : Fin n, ((i.val + 1 : ℕ) : ℤ) ∣ (sievePrefixIntegralLeftTransform n *ᵥ y) i := by
  constructor
  · rintro ⟨x, hx, _⟩
    exact (sievePrefixIntegral_solvable_iff n y).mp ⟨x, hx⟩
  · intro h
    obtain ⟨x, hx⟩ := (sievePrefixIntegral_solvable_iff n y).mpr h
    exact ⟨x, hx, fun y hy => sievePrefixIntegral_injective n (hy.trans hx.symm)⟩

/-- Canonical integral reconstruction when the exact congruences hold. -/
def sievePrefixIntegralReconstruction (n : ℕ) (y : Fin n → ℤ) : Fin n → ℤ :=
  sievePrefixIntegralRightTransform n *ᵥ
    (fun i => (sievePrefixIntegralLeftTransform n *ᵥ y) i / ((i.val + 1 : ℕ) : ℤ))

theorem sievePrefixIntegralReconstruction_iff (n : ℕ) (y : Fin n → ℤ) :
    sievePrefixIntegralRamanujanMatrix n *ᵥ sievePrefixIntegralReconstruction n y = y ↔
      ∀ i : Fin n, ((i.val + 1 : ℕ) : ℤ) ∣ (sievePrefixIntegralLeftTransform n *ᵥ y) i := by
  constructor
  · intro h
    exact (sievePrefixIntegral_solvable_iff n y).mp ⟨_, h⟩
  · intro h
    apply Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr (sievePrefixIntegralLeftTransform_unit n))
    unfold sievePrefixIntegralReconstruction
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      sievePrefixIntegralRamanujanMatrix_reduction]
    ext i
    rw [Matrix.mulVec_diagonal]
    change ((i.val + 1 : ℕ) : ℤ) *
      ((sievePrefixIntegralLeftTransform n *ᵥ y) i / ((i.val + 1 : ℕ) : ℤ)) = _
    rw [mul_comm, Int.ediv_mul_cancel (h i)]

/-- Integer data exposing the final interpolation congruence. -/
def sievePrefixIntegralObstructedData (n : ℕ) : Fin (n + 2) → ℤ :=
  sievePrefixIntegerFloorMatrix (n + 2) *ᵥ
    (fun i => if i = Fin.last (n + 1) then 1 else 0)

theorem sievePrefixIntegralObstructedData_no_solution (n : ℕ) :
    ¬ ∃ x : Fin (n + 2) → ℤ,
      sievePrefixIntegralRamanujanMatrix (n + 2) *ᵥ x = sievePrefixIntegralObstructedData n := by
  intro h
  have hc := (sievePrefixIntegral_solvable_iff (n + 2) _).mp h (Fin.last (n + 1))
  have hF : IsUnit (sievePrefixIntegerFloorMatrix (n + 2)).det := by
    rw [sievePrefixIntegerFloorMatrix_det]
    exact isUnit_one
  have he : sievePrefixIntegralLeftTransform (n + 2) *ᵥ sievePrefixIntegralObstructedData n =
      (fun i => if i = Fin.last (n + 1) then (1 : ℤ) else 0) := by
    rw [sievePrefixIntegralLeftTransform, sievePrefixIntegralObstructedData,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hF, Matrix.one_mulVec]
  rw [he] at hc
  simp only [Fin.val_last] at hc
  have hd : n + 2 ∣ 1 := by exact_mod_cast hc
  have := Nat.le_of_dvd (by omega : 0 < 1) hd
  omega

/-- Every nontrivial integral obstruction is still solvable over the real numbers. -/
theorem sievePrefixIntegralObstructedData_real_solution (n : ℕ) :
    ∃ x : Fin (n + 2) → ℝ, sievePrefixRamanujanMatrix (n + 2) *ᵥ x =
      (fun i => (sievePrefixIntegralObstructedData n i : ℝ)) := by
  have hd : IsUnit (sievePrefixRamanujanMatrix (n + 2)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [sievePrefixRamanujanMatrix_det]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero (n + 2))
  refine ⟨(sievePrefixRamanujanMatrix (n + 2))⁻¹ *ᵥ
    (fun i => (sievePrefixIntegralObstructedData n i : ℝ)), ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]

/-- The complete integer obstruction module, including its zero-dimensional case. -/
theorem sievePrefixIntegral_cokernel (n : ℕ) :
    Nonempty (((Fin n → ℤ) ⧸ LinearMap.range (sievePrefixIntegralRamanujanMatrix n).mulVecLin)
      ≃ₗ[ℤ] ∀ i : Fin n, ℤ ⧸ Ideal.span {((i.val + 1 : ℕ) : ℤ)}) :=
  _root_.HTGeometry.ConstraintRelativity.nonempty_coker_equiv_pi_of_smith
    (sievePrefixIntegralLeftTransform_unit n) (sievePrefixIntegralRightTransform_unit n)
    (fun i : Fin n => ((i.val + 1 : ℕ) : ℤ)) rfl
    (sievePrefixIntegralRamanujanMatrix_reduction n)

theorem sievePrefixIntegral_cokernel_cyclic (n : ℕ) :
    Nonempty (((Fin n → ℤ) ⧸ LinearMap.range (sievePrefixIntegralRamanujanMatrix n).mulVecLin)
      ≃+ ∀ i : Fin n, ZMod (i.val + 1)) := by
  obtain ⟨e⟩ := sievePrefixIntegral_cokernel n
  exact ⟨e.toAddEquiv.trans (AddEquiv.piCongrRight fun i : Fin n =>
    (Int.quotientSpanNatEquivZMod (i.val + 1)).toAddEquiv)⟩

private theorem prefix_prod_initial (n : ℕ) : (∏ i : Fin n, (i.val + 1)) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simpa [Nat.factorial_succ, Nat.mul_comm] using congrArg (fun x => x * (n + 1)) ih

theorem sievePrefixIntegral_cokernel_card (n : ℕ) :
    Nat.card ((Fin n → ℤ) ⧸ LinearMap.range (sievePrefixIntegralRamanujanMatrix n).mulVecLin) =
      n.factorial := by
  obtain ⟨e⟩ := sievePrefixIntegral_cokernel_cyclic n
  rw [Nat.card_congr e.toEquiv, Nat.card_pi]
  simp only [Nat.card_zmod, prefix_prod_initial]

/-- Kernel coordinates for the actual operator over every commutative ring. -/
def sievePrefixIntegralKernelEquiv (n : ℕ) (K : Type*) [CommRing K] :
    {x : Fin n → K // sievePrefixIntegralMatrixOver n K *ᵥ x = 0} ≃
      ∀ i : Fin n, {x : K // ((i.val + 1 : ℕ) : K) * x = 0} :=
  prefix_kernel_diagonal_equiv _ _ _ _
    (prefix_map_det_unit _ (sievePrefixIntegralLeftTransform_unit n))
    (prefix_map_det_unit _ (sievePrefixIntegralRightTransform_unit n))
    (sievePrefixIntegralMatrixOver_reduction n K)

private theorem prefix_actual_modular_kernel_card (n m : ℕ) [NeZero m] :
    Nat.card {x : Fin n → ZMod m // sievePrefixIntegralMatrixOver n (ZMod m) *ᵥ x = 0} =
      ∏ i : Fin n, Nat.gcd m (i.val + 1) := by
  rw [Nat.card_congr (sievePrefixIntegralKernelEquiv n (ZMod m)), Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => prefix_scalar_kernel_card m (i.val + 1)

/-- Exact loss of injectivity at every positive modulus. -/
theorem sievePrefixIntegral_modular_kernel_card (n q : ℕ) :
    Nat.card {x : Fin n → ZMod (q + 1) //
      sievePrefixIntegralMatrixOver n (ZMod (q + 1)) *ᵥ x = 0} =
        ∏ i : Fin n, Nat.gcd (q + 1) (i.val + 1) :=
  prefix_actual_modular_kernel_card n (q + 1)

/-- The prime-power obstruction profile is the truncated factorial valuation sum. -/
theorem sievePrefixIntegral_prime_power_kernel_card (n : ℕ) (p : Nat.Primes) (a : ℕ) :
    Nat.card {x : Fin n → ZMod ((p : ℕ)^a) //
      sievePrefixIntegralMatrixOver n (ZMod ((p : ℕ)^a)) *ᵥ x = 0} =
        (p : ℕ) ^ (∑ r ∈ Finset.range a, n / (p : ℕ)^(r + 1)) := by
  letI : NeZero ((p : ℕ)^a) := ⟨pow_ne_zero _ p.property.ne_zero⟩
  rw [prefix_actual_modular_kernel_card, prefix_gcd_product_prime_power]

/-- Each prime-power step exposes exactly the next floor-counted obstruction layer. -/
theorem sievePrefixIntegral_prime_power_kernel_step (n : ℕ) (p : Nat.Primes) (a : ℕ) :
    Nat.card {x : Fin n → ZMod ((p : ℕ)^(a + 1)) //
      sievePrefixIntegralMatrixOver n (ZMod ((p : ℕ)^(a + 1))) *ᵥ x = 0} =
        (p : ℕ) ^ (n / (p : ℕ)^(a + 1)) *
          Nat.card {x : Fin n → ZMod ((p : ℕ)^a) //
            sievePrefixIntegralMatrixOver n (ZMod ((p : ℕ)^a)) *ᵥ x = 0} := by
  rw [sievePrefixIntegral_prime_power_kernel_card, sievePrefixIntegral_prime_power_kernel_card,
    Finset.sum_range_succ, pow_add]
  exact Nat.mul_comm _ _

/-- Exact rank after reduction modulo any prime. -/
theorem sievePrefixIntegral_mod_prime_rank (n : ℕ) (p : Nat.Primes) :
    (sievePrefixIntegralMatrixOver n (ZMod (p : ℕ))).rank = n - n / (p : ℕ) := by
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  have hU := prefix_map_det_unit (K := ZMod (p : ℕ)) _ (sievePrefixIntegralLeftTransform_unit n)
  have hV := prefix_map_det_unit (K := ZMod (p : ℕ)) _ (sievePrefixIntegralRightTransform_unit n)
  have h := congrArg Matrix.rank (sievePrefixIntegralMatrixOver_reduction n (ZMod (p : ℕ)))
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hV,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hU, prefix_diagonal_prime_rank] at h
  exact h
end
end GaloisForLFunctions.BezoutValuationIncidence
