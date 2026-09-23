import GaloisForLFunctions.RHTower.IrrationalCircleOrderCharge

/-!
# Quadratic circle charge for free reflection orbits

The linear prime-order circle charge cancels on a reflection pair: `q(m)+q(-m)=0`.  Squaring the
signed order before applying the same faithful prime-log character changes the parity:

`q₂(m)+q₂(-m) = [2 m² log p]`.

This phase vanishes exactly when `m=0`.  More generally, the phase of a finite list of free-orbit
multiplicities, `[2 ∑ mᵢ² log p]`, vanishes exactly when every multiplicity is zero.

These are consumer-side algebraic facts.  They do not construct the equivariant quadratic
refinement, fixed-point correction, or source annihilation needed for an RH proof.
-/

namespace RHTower

noncomputable section

/-- Quadratic refinement of the one-prime order circle charge. -/
def quadraticPrimeOrderCircleCharge (p : Nat.Primes) (m : ℤ) : AddCircle (1 : ℝ) :=
  primeOrderCircleCharge p (m ^ (2 : ℕ))

/-- Total quadratic phase of a signed reflection pair. -/
def reflectionPairQuadraticCircleCharge (p : Nat.Primes) (m : ℤ) : AddCircle (1 : ℝ) :=
  quadraticPrimeOrderCircleCharge p m + quadraticPrimeOrderCircleCharge p (-m)

/-- Reflection-pair quadratic phase is the prime circle charge of `2m²`. -/
theorem reflectionPairQuadraticCircleCharge_eq (p : Nat.Primes) (m : ℤ) :
    reflectionPairQuadraticCircleCharge p m = primeOrderCircleCharge p (2 * m ^ (2 : ℕ)) := by
  rw [reflectionPairQuadraticCircleCharge, quadraticPrimeOrderCircleCharge,
    quadraticPrimeOrderCircleCharge, neg_sq]
  change GaloisForLFunctions.RHTower.primeCircleHom (Finsupp.single p (m ^ (2 : ℕ))) +
      GaloisForLFunctions.RHTower.primeCircleHom (Finsupp.single p (m ^ (2 : ℕ))) = _
  rw [← map_add]
  congr 1
  ext q
  by_cases hq : q = p <;> simp [hq, two_mul]

/-- Unlike the linear phase, the reflection-pair quadratic phase vanishes only at zero order. -/
theorem reflectionPairQuadraticCircleCharge_eq_zero_iff (p : Nat.Primes) (m : ℤ) :
    reflectionPairQuadraticCircleCharge p m = 0 ↔ m = 0 := by
  rw [reflectionPairQuadraticCircleCharge_eq,
    primeOrderCircleCharge_eq_zero_iff]
  simp

/-- Quadratic phase of the full reflected local Xi pair through a point. -/
def xiReflectionPairQuadraticCircleCharge (p : Nat.Primes) (ρ : ℂ) : AddCircle (1 : ℝ) :=
  reflectionPairQuadraticCircleCharge p ((analyticOrderAt xi ρ).toNat : ℤ)

theorem xiReflectionPairQuadraticCircleCharge_eq_zero_iff (p : Nat.Primes) (ρ : ℂ) :
    xiReflectionPairQuadraticCircleCharge p ρ = 0 ↔
      (analyticOrderAt xi ρ).toNat = 0 := by
  rw [xiReflectionPairQuadraticCircleCharge,
    reflectionPairQuadraticCircleCharge_eq_zero_iff]
  simp

/-- For any fixed prime, vanishing of the quadratic reflected-pair phase at every right-half Xi
zero is equivalent to RH. -/
theorem riemannHypothesis_iff_xiReflectionPairQuadraticCircleCharges_zero
    (p : Nat.Primes) :
    RiemannHypothesis ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 → xiReflectionPairQuadraticCircleCharge p ρ = 0 := by
  constructor
  · intro hRH ρ hρ hzero
    exact (rh_iff_xi_ne_zero_right.mp hRH ρ hρ hzero).elim
  · intro hclose
    apply rh_iff_xi_ne_zero_right.mpr
    intro ρ hρ hzero
    have hc := hclose ρ hρ hzero
    have hord := (xiReflectionPairQuadraticCircleCharge_eq_zero_iff p ρ).mp hc
    exact (xi_order_toNat_ne_zero hzero hord).elim

/-- Nonnegative integer carried by a finite list of free-orbit multiplicities. -/
def freeOrbitQuadraticIndex (ms : List ℕ) : ℕ :=
  2 * (ms.map fun m => m ^ (2 : ℕ)).sum

theorem sum_sq_eq_zero_iff (ms : List ℕ) :
    (ms.map fun m => m ^ (2 : ℕ)).sum = 0 ↔ ∀ m ∈ ms, m = 0 := by
  induction ms with
  | nil => simp
  | cons a ms ih => simp [ih]

/-- The free-orbit quadratic index is zero exactly when every listed multiplicity is zero. -/
theorem freeOrbitQuadraticIndex_eq_zero_iff (ms : List ℕ) :
    freeOrbitQuadraticIndex ms = 0 ↔ ∀ m ∈ ms, m = 0 := by
  rw [freeOrbitQuadraticIndex, mul_eq_zero]
  simp [sum_sq_eq_zero_iff]

/-- Circle phase of the finite free-orbit quadratic index. -/
def freeOrbitQuadraticCircleCharge (p : Nat.Primes) (ms : List ℕ) : AddCircle (1 : ℝ) :=
  primeOrderCircleCharge p (freeOrbitQuadraticIndex ms)

/-- A single irrational prime-log phase detects whether a finite free-orbit multiplicity list is
identically zero. -/
theorem freeOrbitQuadraticCircleCharge_eq_zero_iff (p : Nat.Primes) (ms : List ℕ) :
    freeOrbitQuadraticCircleCharge p ms = 0 ↔ ∀ m ∈ ms, m = 0 := by
  rw [freeOrbitQuadraticCircleCharge, primeOrderCircleCharge_eq_zero_iff]
  norm_cast
  exact freeOrbitQuadraticIndex_eq_zero_iff ms

/-! ### Polarization-symmetry firewall -/

/-- Polarization of an arbitrary function between additive groups. -/
def quadraticPolarization {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (q : A → B) (x y : A) : B := q (x + y) - q x - q y

/-- Every quadratic polarization on an abelian group is symmetric. -/
theorem quadraticPolarization_comm {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (q : A → B) (x y : A) :
    quadraticPolarization q x y = quadraticPolarization q y x := by
  unfold quadraticPolarization
  rw [add_comm x y]
  abel

/-- If a quadratic polarization is also antisymmetric at one pair, its value there is two-torsion. -/
theorem two_nsmul_quadraticPolarization_eq_zero_of_antisymm
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (q : A → B) (x y : A)
    (hanti : quadraticPolarization q x y = -quadraticPolarization q y x) :
    2 • quadraticPolarization q x y = 0 := by
  have hself : quadraticPolarization q x y = -quadraticPolarization q x y := by
    exact hanti.trans (congrArg Neg.neg (quadraticPolarization_comm q y x))
  simpa [two_nsmul] using (eq_neg_iff_add_eq_zero.mp hself)

theorem primeOrderCircleCharge_add (p : Nat.Primes) (m n : ℤ) :
    primeOrderCircleCharge p (m + n) =
      primeOrderCircleCharge p m + primeOrderCircleCharge p n := by
  rw [primeOrderCircleCharge, primeOrderCircleCharge, primeOrderCircleCharge,
    Finsupp.single_add, map_add]

/-- The prime-log circle phase is not two-torsion. -/
theorem two_nsmul_primeOrderCircleCharge_one_ne_zero (p : Nat.Primes) :
    2 • primeOrderCircleCharge p 1 ≠ 0 := by
  have h : primeOrderCircleCharge p 2 ≠ 0 :=
    (primeOrderCircleCharge_eq_zero_iff p 2).not.mpr (by norm_num)
  intro hz
  apply h
  calc
    primeOrderCircleCharge p 2 = primeOrderCircleCharge p (1 + 1) := by norm_num
    _ = primeOrderCircleCharge p 1 + primeOrderCircleCharge p 1 :=
      primeOrderCircleCharge_add p 1 1
    _ = 2 • primeOrderCircleCharge p 1 := by simp [two_nsmul]
    _ = 0 := hz

/-- A non-two-torsion prime-log phase cannot be the polarization of an antisymmetric weld pairing.
The circle-valued quadratic route therefore needs a separate symmetric incidence form. -/
theorem no_primeCircle_antisymmetric_quadraticPolarization
    {A : Type*} [AddCommGroup A] (p : Nat.Primes)
    (q : A → AddCircle (1 : ℝ)) (x y : A)
    (hvalue : quadraticPolarization q x y = primeOrderCircleCharge p 1)
    (hanti : quadraticPolarization q x y = -quadraticPolarization q y x) : False := by
  have hz := two_nsmul_quadraticPolarization_eq_zero_of_antisymm q x y hanti
  rw [hvalue] at hz
  exact two_nsmul_primeOrderCircleCharge_one_ne_zero p hz

end


end RHTower
