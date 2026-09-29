import GaloisForLFunctions.HTGeometry.TriangularLineFieldInvariants
import GaloisForLFunctions.HTGeometry.RittLogTowerScaleInvariantRigidity

/-!
# The jet ratios of a function with a given logarithmic derivative

If `v' = x·v`, then every jet of `v` is `v` times a universal polynomial in the jets of `x`:

`v^{(k)} = v · B_k(x, x', …, x^{(k−1)})`,   `B_0 = 1`,   `B_{k+1} = D B_k + x_0·B_k`,

where `D` is the total derivative `x_j ↦ x_{j+1}` of the jet ring.  These are the complete Bell
polynomials in the jets of the logarithmic derivative.

In the ring `K[x_0, …, x_{n−1}]` the total derivative is truncated (`x_{n−1} ↦ 0`); for `k ≤ n` the
polynomial `B_k` only involves `x_0, …, x_{k−1}`, so the truncation is invisible.  The family
`(B_0, …, B_{n−1})` is unitriangular (`∂B_{j+1}/∂x_j = 1`), and `B_k` is weighted homogeneous of
weight `k` for the weight `w(x_j) = j + 1`.

The polynomials are defined over any commutative semiring; over `ℕ` they have constant coefficients
for every derivation, which gives the chain rule for the jets inside a Ritt frame.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Generic

variable (R : Type*) [CommSemiring R] (n : ℕ)

/-- The image of the jet variable `x_j` under the truncated total derivative. -/
def bellShiftTarget (j : Fin n) : MvPolynomial (Fin n) R :=
  if h : (j : ℕ) + 1 < n then X ⟨(j : ℕ) + 1, h⟩ else 0

/-- The truncated total derivative `x_j ↦ x_{j+1}` of the jet ring. -/
def bellShiftDeriv : Derivation R (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R) :=
  mkDerivation R (bellShiftTarget R n)

/-- The first jet variable `x_0` (zero in the empty ring). -/
def bellJetZero : MvPolynomial (Fin n) R := if h : 0 < n then X ⟨0, h⟩ else 0

/-- **The complete Bell polynomials of the jets of a logarithmic derivative.** -/
def connBell : ℕ → MvPolynomial (Fin n) R
  | 0 => 1
  | k + 1 => bellShiftDeriv R n (connBell k) + bellJetZero R n * connBell k

theorem connBell_zero : connBell R n 0 = 1 := rfl

theorem connBell_succ (k : ℕ) :
    connBell R n (k + 1) = bellShiftDeriv R n (connBell R n k) + bellJetZero R n * connBell R n k :=
  rfl

theorem bellShiftDeriv_X (j : Fin n) : bellShiftDeriv R n (X j) = bellShiftTarget R n j :=
  mkDerivation_X R _ j

end Generic

/-! ### Change of coefficients -/

section MapCoeff

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (n : ℕ)

theorem map_jetShiftTarget (j : Fin n) :
    map φ (bellShiftTarget R n j) = bellShiftTarget S n j := by
  unfold bellShiftTarget
  split_ifs <;> simp

theorem map_jetZero : map φ (bellJetZero R n) = bellJetZero S n := by
  unfold bellJetZero
  split_ifs <;> simp

theorem map_jetShiftDeriv (Q : MvPolynomial (Fin n) R) :
    map φ (bellShiftDeriv R n Q) = bellShiftDeriv S n (map φ Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [bellShiftDeriv]
  | add P Q hP hQ => rw [map_add, map_add, map_add, hP, hQ, map_add]
  | mul_X P k hP =>
      rw [Derivation.leibniz, map_mul, map_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hP, bellShiftDeriv_X,
        bellShiftDeriv_X, map_jetShiftTarget, map_X]

theorem map_connBell (k : ℕ) : map φ (connBell R n k) = connBell S n k := by
  induction k with
  | zero => simp [connBell_zero]
  | succ k ih => rw [connBell_succ, connBell_succ, map_add, map_mul, map_jetShiftDeriv, ih,
      map_jetZero]

end MapCoeff

/-! ### Unitriangularity -/

section Triangular

variable (K : Type*) [Field K] (n : ℕ)

theorem pderiv_jetShiftTarget (j i : Fin n) :
    pderiv j (bellShiftTarget K n i) = if (j : ℕ) = (i : ℕ) + 1 then 1 else 0 := by
  unfold bellShiftTarget
  by_cases h1 : (i : ℕ) + 1 < n
  · rw [dif_pos h1, pderiv_X, Pi.single_apply]
    by_cases h2 : (j : ℕ) = (i : ℕ) + 1
    · rw [if_pos (Fin.ext h2.symm), if_pos h2]
    · rw [if_neg (fun h => h2 (congrArg Fin.val h).symm), if_neg h2]
  · rw [dif_neg h1, map_zero, if_neg (by have := j.isLt; omega)]

/-- **The commutator of a partial derivative with the total derivative.** -/
theorem commutator_pderiv_jetShiftDeriv (j : Fin n) :
    ⁅(pderiv j : Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K)),
        bellShiftDeriv K n⁆
      = if h : 0 < (j : ℕ) then pderiv ⟨(j : ℕ) - 1, by omega⟩ else 0 := by
  refine derivation_ext fun i => ?_
  rw [Derivation.commutator_apply, bellShiftDeriv_X, pderiv_jetShiftTarget, pderiv_X]
  have hδ : bellShiftDeriv K n (Pi.single (M := fun _ => MvPolynomial (Fin n) K) j 1 i) = 0 := by
    rw [Pi.single_apply]
    split_ifs <;> simp
  rw [hδ, sub_zero]
  by_cases hj : 0 < (j : ℕ)
  · rw [dif_pos hj, pderiv_X, Pi.single_apply]
    by_cases h2 : (j : ℕ) = (i : ℕ) + 1
    · rw [if_pos h2, if_pos (Fin.ext (by simp; omega))]
    · rw [if_neg h2, if_neg (fun h => h2 (by rw [h]; simp; omega))]
  · rw [dif_neg hj, if_neg (by omega)]
    rfl

theorem pderiv_jetShiftDeriv (j : Fin n) (P : MvPolynomial (Fin n) K) :
    pderiv j (bellShiftDeriv K n P)
      = bellShiftDeriv K n (pderiv j P)
        + if h : 0 < (j : ℕ) then pderiv ⟨(j : ℕ) - 1, by omega⟩ P else 0 := by
  have h := congrArg (fun D : Derivation K (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K) => D P)
    (commutator_pderiv_jetShiftDeriv K n j)
  simp only [Derivation.commutator_apply] at h
  rw [eq_add_of_sub_eq' h]
  by_cases hj : 0 < (j : ℕ)
  · rw [dif_pos hj, dif_pos hj]
  · rw [dif_neg hj, dif_neg hj]
    rfl

theorem pderiv_jetZero (j : Fin n) :
    pderiv j (bellJetZero K n) = if (j : ℕ) = 0 then 1 else 0 := by
  unfold bellJetZero
  by_cases h1 : 0 < n
  · rw [dif_pos h1, pderiv_X, Pi.single_apply]
    by_cases h2 : (j : ℕ) = 0
    · rw [if_pos (Fin.ext h2.symm), if_pos h2]
    · rw [if_neg (fun h => h2 (congrArg Fin.val h).symm), if_neg h2]
  · exact absurd j.isLt (by omega)

/-- **The Bell polynomials are unitriangular.** -/
theorem connBell_triangular (k : ℕ) :
    (∀ j : Fin n, k ≤ (j : ℕ) → pderiv j (connBell K n k) = 0) ∧
      (∀ j : Fin n, (j : ℕ) + 1 = k → pderiv j (connBell K n k) = 1) := by
  induction k with
  | zero =>
      refine ⟨fun j _ => by rw [connBell_zero, pderiv_one], fun j hj => by omega⟩
  | succ k ih =>
      obtain ⟨ih0, ih1⟩ := ih
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · rw [connBell_succ, map_add, pderiv_jetShiftDeriv, ih0 j (by omega), map_zero, zero_add,
          Derivation.leibniz, ih0 j (by omega), smul_zero, zero_add, smul_eq_mul, pderiv_jetZero,
          if_neg (by omega), mul_zero, add_zero]
        split_ifs with h
        · exact ih0 _ (by simp; omega)
        · rfl
      · rw [connBell_succ, map_add, pderiv_jetShiftDeriv, ih0 j (by omega), map_zero, zero_add,
          Derivation.leibniz, ih0 j (by omega), smul_zero, zero_add, smul_eq_mul, pderiv_jetZero]
        by_cases hk : k = 0
        · subst hk
          have hj0 : (j : ℕ) = 0 := by omega
          rw [dif_neg (by omega), if_pos hj0, connBell_zero, mul_one, zero_add]
        · rw [dif_pos (by omega), if_neg (by omega), mul_zero, add_zero]
          exact ih1 _ (by simp; omega)

theorem isUnitriangularField_connBell :
    IsUnitriangularField (fun i : Fin n => connBell K n i) where
  zero i hi := by simp only [hi, connBell_zero]
  low i j hij := (connBell_triangular K n i).1 j hij
  sub i j hij := (connBell_triangular K n i).2 j hij

end Triangular

/-! ### The weight -/

section Weight

variable {K : Type*} [Field K] (n : ℕ)

theorem jetWeightScale_X (c : K) (j : Fin n) :
    RittFrame.jetWeightScale n c (X j) = C (c ^ ((j : ℕ) + 1)) * X j := by
  rw [RittFrame.jetWeightScale, aeval_X]

theorem jetWeightScale_jetShiftTarget (c : K) (j : Fin n) :
    RittFrame.jetWeightScale n c (bellShiftTarget K n j)
      = C (c ^ ((j : ℕ) + 2)) * bellShiftTarget K n j := by
  unfold bellShiftTarget
  split_ifs with h
  · rw [jetWeightScale_X]
  · simp

/-- **The total derivative raises the weight by one.** -/
theorem jetWeightScale_jetShiftDeriv (c : K) (P : MvPolynomial (Fin n) K) :
    RittFrame.jetWeightScale n c (bellShiftDeriv K n P)
      = C c * bellShiftDeriv K n (RittFrame.jetWeightScale n c P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [bellShiftDeriv]
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, map_add, map_add, mul_add]
  | mul_X P k hP =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hP,
        bellShiftDeriv_X, jetWeightScale_jetShiftTarget, map_mul, jetWeightScale_X,
        Derivation.leibniz, smul_eq_mul, smul_eq_mul, Derivation.leibniz, smul_eq_mul,
        smul_eq_mul, derivation_C, bellShiftDeriv_X, mul_zero, add_zero]
      simp only [pow_succ, map_mul]
      ring

theorem jetWeightScale_jetZero (c : K) :
    RittFrame.jetWeightScale n c (bellJetZero K n) = C c * bellJetZero K n := by
  unfold bellJetZero
  split_ifs with h
  · rw [jetWeightScale_X]
    simp
  · simp

/-- **`B_k` has weight `k`.** -/
theorem jetWeightScale_connBell (c : K) (k : ℕ) :
    RittFrame.jetWeightScale n c (connBell K n k) = C (c ^ k) * connBell K n k := by
  induction k with
  | zero => simp [connBell_zero]
  | succ k ih =>
      rw [connBell_succ, map_add, map_mul, jetWeightScale_jetShiftDeriv, ih, jetWeightScale_jetZero,
        Derivation.leibniz, derivation_C, smul_zero, add_zero, smul_eq_mul, pow_succ, map_mul]
      ring

/-- The weight scaling multiplies each coefficient by the weight power. -/
theorem coeff_jetWeightScale (c : K) (P : MvPolynomial (Fin n) K) (e : Fin n →₀ ℕ) :
    coeff e (RittFrame.jetWeightScale n c P)
      = c ^ (Finsupp.weight (RittFrame.jetWeight n) e) * coeff e P := by
  classical
  have hmono : ∀ (d : Fin n →₀ ℕ) (a : K), RittFrame.jetWeightScale n c (monomial d a)
      = monomial d (c ^ (Finsupp.weight (RittFrame.jetWeight n) d) * a) := by
    intro d a
    have hw : IsWeightedHomogeneous (RittFrame.jetWeight n) (monomial d a : MvPolynomial (Fin n) K)
        (Finsupp.weight (RittFrame.jetWeight n) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    have h := aeval_weight_scaling (RittFrame.jetWeight n) hw c
    rw [C_mul_monomial] at h
    exact h
  conv_lhs => rw [P.as_sum, map_sum]
  simp only [hmono, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl]
  · intro d _ hd
    rw [if_neg hd]
  · intro he
    rw [if_pos rfl, notMem_support_iff.mp he, mul_zero]

end Weight

/-! ### The jets inside a Ritt frame -/

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (Fr : RittFrame K L)

/-- **Chain rule for polynomials with natural coefficients.** -/
theorem d_aeval_map_nat {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → L)
    (Q : MvPolynomial ι ℕ) :
    Fr.d (aeval g (map (Nat.castRingHom K) Q))
      = ∑ i, aeval g (map (Nat.castRingHom K) (pderiv i Q)) * Fr.d (g i) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
      simp only [map_C, aeval_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
      rw [Fr.d_base, eq_natCast, Fr.dK_natCast, map_zero]
  | add P Q hP hQ =>
      rw [map_add, map_add, Fr.d_add, hP, hQ, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add, map_add, map_add, add_mul]
  | mul_X P k hP =>
      rw [map_mul, map_X, map_mul, aeval_X, Fr.d_mul, hP, Finset.sum_mul]
      have hterm : ∀ i, aeval g (map (Nat.castRingHom K) (pderiv i (P * X k))) * Fr.d (g i)
          = aeval g (map (Nat.castRingHom K) (pderiv i P)) * Fr.d (g i) * g k
            + if i = k then aeval g (map (Nat.castRingHom K) P) * Fr.d (g k) else 0 := by
        intro i
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_X]
        by_cases hik : i = k
        · subst hik
          simp only [Pi.single_eq_same, map_add, map_mul, map_X, aeval_X, map_one, if_true]
          ring
        · have hki : ¬ k = i := fun h => hik h.symm
          simp only [Pi.single_apply, hki, hik, if_false, map_add, map_mul, map_X, aeval_X,
            map_zero]
          ring
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]

theorem aeval_jetShiftTarget {u : L} {n : ℕ} (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    aeval (Fr.jetFamily u n) (bellShiftTarget K n j) = Fr.d^[(j : ℕ) + 1] u := by
  rw [bellShiftTarget, dif_pos hj, aeval_X]
  rfl

theorem iterate_d_add (x y : L) : ∀ k : ℕ, Fr.d^[k] (x + y) = Fr.d^[k] x + Fr.d^[k] y := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, Fr.d_add]

/-- **The jets of a function with logarithmic derivative `u`.**  If `d v = u·v` then
`d^k v = v·B_k(u, du, …)` for `k ≤ n`. -/
theorem iterate_d_eq_mul_connBell {u v : L} (hv : Fr.d v = u * v) (n : ℕ) :
    ∀ k : ℕ, k ≤ n → Fr.d^[k] v = v * aeval (Fr.jetFamily u n) (connBell K n k) := by
  intro k
  induction k with
  | zero => intro _; rw [connBell_zero, map_one, mul_one]; rfl
  | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      rw [Function.iterate_succ_apply', ih (by omega), Fr.d_mul, hv, connBell_succ, map_add,
        map_mul]
      -- the derivative of the Bell polynomial
      have hchain : Fr.d (aeval (Fr.jetFamily u n) (connBell K n k))
          = aeval (Fr.jetFamily u n) (bellShiftDeriv K n (connBell K n k)) := by
        have hexp : ∀ P : MvPolynomial (Fin n) K,
            bellShiftDeriv K n P = ∑ i, pderiv i P * bellShiftDeriv K n (X i) := fun P => by
          simpa [aeval_X_left_apply] using derivation_aeval_eq_sum_pderiv (bellShiftDeriv K n) X P
        rw [hexp, map_sum, ← map_connBell (Nat.castRingHom K) n k, Fr.d_aeval_map_nat]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← pderiv_map, map_connBell, map_mul, bellShiftDeriv_X]
        by_cases hi : (i : ℕ) + 1 < n
        · rw [aeval_jetShiftTarget Fr i hi]
          show _ * Fr.d (Fr.d^[(i : ℕ)] u) = _
          rw [← Function.iterate_succ_apply' Fr.d]
        · have hzero : pderiv i (connBell K n k) = 0 :=
            (connBell_triangular K n k).1 i (by omega)
          rw [hzero, map_zero, zero_mul, zero_mul]
      have hzero' : aeval (Fr.jetFamily u n) (bellJetZero K n) = u := by
        rw [bellJetZero, dif_pos (by omega), aeval_X]
        rfl
      rw [hchain, hzero']
      ring

end RittFrame

end

end GaloisForLFunctions.HTGeometry
