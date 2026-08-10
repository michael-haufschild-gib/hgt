import GaloisForLFunctions.HTGeometry.AbelianZetaGas.GasWord
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.KMSExchange

/-!
# The gas algebra and its Gibbs functional

The monomial `*`-algebra of the gas is the monoid algebra of the monomial monoid.  The imaginary
time flow is the algebra automorphism scaling each monomial by its charge weight, and the Gibbs
functional reads off the diagonal monomials with the weight `∏_i q_i^{n_i}`.  This file builds the
weight layer: the charge weight is multiplicative, the diagonality of a product is symmetric in the
two factors, and the two together give the exchange identity on weights, which is the KMS boundary
condition read on monomials.
-/

namespace GaloisForLFunctions.HTGeometry

namespace GasWord

variable {M : Type*}

/-! ## Integer exponents and the charge weight -/

/-- Exponents of a monomial read in `ℤ`. -/
noncomputable def natToInt (f : M →₀ ℕ) : M →₀ ℤ :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) f

@[simp] theorem natToInt_apply (f : M →₀ ℕ) (i : M) : natToInt f i = (f i : ℤ) :=
  Finsupp.mapRange_apply

theorem charge_eq_sub (x : GasWord M) :
    charge x = natToInt x.raise - natToInt x.lower := by
  refine Finsupp.ext fun i => ?_
  rw [charge_apply, Finsupp.sub_apply, natToInt_apply, natToInt_apply]

/-- The multiplicative weight attached to an integer exponent family. -/
noncomputable def zprod (q : M → ℂ) (f : M →₀ ℤ) : ℂ := f.prod fun i k => q i ^ k

@[simp] theorem zprod_zero (q : M → ℂ) : zprod q 0 = 1 := by
  rw [zprod, Finsupp.prod_zero_index]

/-- **The weight is multiplicative in the exponents.** -/
theorem zprod_add (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (f g : M →₀ ℤ) :
    zprod q (f + g) = zprod q f * zprod q g :=
  Finsupp.prod_add_index' (fun i => zpow_zero (q i)) (fun i a b => zpow_add₀ (hq i) a b)

/-! ## The Gibbs weight of a monomial -/

open Classical in
/-- The Gibbs weight of a monomial: `∏_i q_i^{n_i}` on the diagonal monomials, zero elsewhere. -/
noncomputable def gibbsWeight (q : M → ℂ) (x : GasWord M) : ℂ :=
  if x.raise = x.lower then zprod q (natToInt x.raise) else 0

theorem gibbsWeight_of_diag {q : M → ℂ} {x : GasWord M} (h : x.raise = x.lower) :
    gibbsWeight q x = zprod q (natToInt x.raise) := by
  classical
  rw [gibbsWeight, if_pos h]

theorem gibbsWeight_of_not_diag {q : M → ℂ} {x : GasWord M} (h : ¬ x.raise = x.lower) :
    gibbsWeight q x = 0 := by
  classical
  rw [gibbsWeight, if_neg h]

@[simp] theorem gibbsWeight_one (q : M → ℂ) : gibbsWeight q (1 : GasWord M) = 1 := by
  rw [gibbsWeight_of_diag (by rfl)]
  show zprod q (natToInt (0 : M →₀ ℕ)) = 1
  have : natToInt (0 : M →₀ ℕ) = 0 := by
    refine Finsupp.ext fun i => ?_
    simp
  rw [this, zprod_zero]

/-! ## Diagonality is symmetric in a product -/

theorem diag_iff_charge (x : GasWord M) : x.raise = x.lower ↔ charge x = 0 :=
  (charge_eq_zero_iff x).symm

/-- **A product is diagonal exactly when the reversed product is.** -/
theorem diag_mul_comm (x y : GasWord M) :
    (x * y).raise = (x * y).lower ↔ (y * x).raise = (y * x).lower := by
  rw [diag_iff_charge, diag_iff_charge, charge_mul, charge_mul, add_comm]

/-! ## The exchange identity on weights -/

/-- On a diagonal product the exponents of the two orders differ by exactly the charge of the
first factor. -/
theorem natToInt_raise_mul_eq (x y : GasWord M)
    (hdiag : (x * y).raise = (x * y).lower) :
    natToInt (x * y).raise = charge x + natToInt (y * x).raise := by
  refine Finsupp.ext fun i => ?_
  have hi : (x * y).raise i = (x * y).lower i := by rw [hdiag]
  rw [raise_apply_mul, lower_apply_mul] at hi
  rw [natToInt_apply, Finsupp.add_apply, charge_apply, natToInt_apply,
    raise_apply_mul, raise_apply_mul]
  omega

/-- **The KMS exchange identity, read on monomial weights.**  Reversing a product multiplies its
Gibbs weight by the charge weight of the factor moved across. -/
theorem gibbsWeight_exchange (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (x y : GasWord M) :
    gibbsWeight q (x * y) = zprod q (charge x) * gibbsWeight q (y * x) := by
  classical
  by_cases hdiag : (x * y).raise = (x * y).lower
  · have hdiag' : (y * x).raise = (y * x).lower := (diag_mul_comm x y).mp hdiag
    rw [gibbsWeight_of_diag hdiag, gibbsWeight_of_diag hdiag',
      natToInt_raise_mul_eq x y hdiag, zprod_add q hq]
  · have hdiag' : ¬ (y * x).raise = (y * x).lower := fun h => hdiag ((diag_mul_comm x y).mpr h)
    rw [gibbsWeight_of_not_diag hdiag, gibbsWeight_of_not_diag hdiag', mul_zero]

/-! ## The adjoint of a monomial -/

/-- The adjoint of a monomial: swap the isometries and their adjoints. -/
def wstar (x : GasWord M) : GasWord M := ⟨x.lower, x.raise⟩

@[simp] theorem wstar_raise (x : GasWord M) : (wstar x).raise = x.lower := rfl

@[simp] theorem wstar_lower (x : GasWord M) : (wstar x).lower = x.raise := rfl

@[simp] theorem wstar_wstar (x : GasWord M) : wstar (wstar x) = x := rfl

@[simp] theorem wstar_one : wstar (1 : GasWord M) = 1 := rfl

theorem wstar_involutive : Function.Involutive (wstar (M := M)) := fun _ => rfl

theorem wstar_injective : Function.Injective (wstar (M := M)) :=
  wstar_involutive.injective

/-- **The adjoint reverses products.** -/
theorem wstar_mul (x y : GasWord M) : wstar (x * y) = wstar y * wstar x := by
  refine GasWord.ext ?_ ?_ <;> refine Finsupp.ext fun i => ?_
  · rw [wstar_raise, lower_apply_mul, raise_apply_mul, wstar_raise, wstar_raise, wstar_lower]
  · rw [wstar_lower, raise_apply_mul, lower_apply_mul, wstar_lower, wstar_lower, wstar_raise]

@[simp] theorem wstar_gen (i : M) : wstar (gen i) = cogen i := rfl

@[simp] theorem wstar_cogen (i : M) : wstar (cogen i) = gen i := rfl

/-- **The Gibbs weight is adjoint-invariant.**  A monomial and its adjoint carry the same weight,
so the Gibbs functional is hermitian on real weights. -/
theorem gibbsWeight_wstar (q : M → ℂ) (x : GasWord M) :
    gibbsWeight q (wstar x) = gibbsWeight q x := by
  classical
  by_cases hdiag : x.raise = x.lower
  · have hd : (wstar x).raise = (wstar x).lower := by
      rw [wstar_raise, wstar_lower, hdiag]
    rw [gibbsWeight_of_diag hd, gibbsWeight_of_diag hdiag, wstar_raise, hdiag]
  · have hd : ¬ (wstar x).raise = (wstar x).lower := by
      rw [wstar_raise, wstar_lower]
      exact fun h => hdiag h.symm
    rw [gibbsWeight_of_not_diag hd, gibbsWeight_of_not_diag hdiag]

/-- The charge changes sign under the adjoint. -/
theorem charge_wstar (x : GasWord M) : charge (wstar x) = -charge x := by
  refine Finsupp.ext fun i => ?_
  rw [charge_apply, Finsupp.neg_apply, charge_apply, wstar_raise, wstar_lower]
  ring

end GasWord

/-! ## The gas algebra -/

open GasWord

variable {M : Type*}

/-- The monomial algebra of the gas: the monoid algebra of the monomial monoid. -/
abbrev GasAlgebra (M : Type*) := MonoidAlgebra ℂ (GasWord M)

/-- The charge weight of a monomial: the factor the modular flow multiplies it by at imaginary
time. -/
noncomputable def chi (q : M → ℂ) (x : GasWord M) : ℂ := zprod q (charge x)

@[simp] theorem chi_one (q : M → ℂ) : chi q (1 : GasWord M) = 1 := by
  rw [chi, charge_one, zprod_zero]

theorem chi_mul (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (x y : GasWord M) :
    chi q (x * y) = chi q x * chi q y := by
  rw [chi, chi, chi, charge_mul, zprod_add q hq]

/-- The modular flow at imaginary time, as a monoid homomorphism into the algebra. -/
noncomputable def twistHom (q : M → ℂ) (hq : ∀ i, q i ≠ 0) : GasWord M →* GasAlgebra M where
  toFun x := MonoidAlgebra.single x (chi q x)
  map_one' := by
    show MonoidAlgebra.single (1 : GasWord M) (chi q 1) = 1
    rw [chi_one, MonoidAlgebra.one_def]
  map_mul' x y := by
    show MonoidAlgebra.single (x * y) (chi q (x * y))
      = MonoidAlgebra.single x (chi q x) * MonoidAlgebra.single y (chi q y)
    rw [MonoidAlgebra.single_mul_single, chi_mul q hq]

/-- **The modular flow at imaginary time.**  It scales every monomial by its charge weight. -/
noncomputable def twist (q : M → ℂ) (hq : ∀ i, q i ≠ 0) : GasAlgebra M →ₐ[ℂ] GasAlgebra M :=
  MonoidAlgebra.lift ℂ (GasAlgebra M) (GasWord M) (twistHom q hq)

theorem twist_single (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (x : GasWord M) (c : ℂ) :
    twist q hq (MonoidAlgebra.single x c) = MonoidAlgebra.single x (c * chi q x) := by
  rw [twist, MonoidAlgebra.lift_single]
  exact MonoidAlgebra.smul_single' c x (chi q x)

/-- The coefficient family of an element of the gas algebra, as a linear map. -/
noncomputable def gasCoeff : GasAlgebra M →ₗ[ℂ] (GasWord M →₀ ℂ) where
  toFun a := a.coeff
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The Gibbs functional.**  It reads off the diagonal monomials with the weight
`∏_i q_i^{n_i}`. -/
noncomputable def gibbs (q : M → ℂ) : GasAlgebra M →ₗ[ℂ] ℂ :=
  (Finsupp.linearCombination ℂ (gibbsWeight q)).comp gasCoeff

theorem gibbs_single (q : M → ℂ) (x : GasWord M) (c : ℂ) :
    gibbs q (MonoidAlgebra.single x c) = c * gibbsWeight q x := by
  show Finsupp.linearCombination ℂ (gibbsWeight q) (MonoidAlgebra.single x c).coeff
    = c * gibbsWeight q x
  show Finsupp.linearCombination ℂ (gibbsWeight q) (Finsupp.single x c) = c * gibbsWeight q x
  rw [Finsupp.linearCombination_single, smul_eq_mul]

@[simp] theorem gibbs_one (q : M → ℂ) : gibbs q (1 : GasAlgebra M) = 1 := by
  rw [MonoidAlgebra.one_def, gibbs_single, gibbsWeight_one, mul_one]

/-- **Existence: the Gibbs functional satisfies the KMS exchange identity.**  This is the
`ULF-IPKMS-1` boundary condition `φ(ab) = φ(b·σ(a))` for the whole gas, at every temperature — no
convergence enters, because the monomial algebra is the algebraic tensor product. -/
theorem gibbs_exchange (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (a b : GasAlgebra M) :
    gibbs q (a * b) = gibbs q (b * twist q hq a) := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [add_mul, map_add, hf, hg, map_add, mul_add, map_add]
  | single x α =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg =>
      rw [mul_add, map_add, hf, hg, add_mul, map_add]
    | single y β =>
      rw [MonoidAlgebra.single_mul_single, gibbs_single, twist_single,
        MonoidAlgebra.single_mul_single, gibbs_single, gibbsWeight_exchange q hq x y]
      show α * β * (zprod q (charge x) * gibbsWeight q (y * x))
        = β * (α * chi q x) * gibbsWeight q (y * x)
      rw [chi]
      ring

/-! ## The generators -/

/-- The isometry of mode `i` inside the gas algebra. -/
noncomputable def gasV (i : M) : GasAlgebra M := MonoidAlgebra.single (gen i) 1

/-- Its adjoint. -/
noncomputable def gasW (i : M) : GasAlgebra M := MonoidAlgebra.single (cogen i) 1

/-- **The isometry relation inside the algebra.** -/
theorem gasW_mul_gasV (i : M) : gasW i * gasV i = 1 := by
  rw [gasW, gasV, MonoidAlgebra.single_mul_single, cogen_mul_gen, mul_one,
    MonoidAlgebra.one_def]

theorem charge_gen (i : M) : charge (gen i) = Finsupp.single i 1 := by
  refine Finsupp.ext fun j => ?_
  rw [charge_apply]
  by_cases hij : i = j
  · subst hij
    simp [gen]
  · have h1 : (gen i).raise j = 0 := by
      show (Finsupp.single i 1 : M →₀ ℕ) j = 0
      exact Finsupp.single_eq_of_ne (Ne.symm hij)
    have h2 : (gen i).lower j = 0 := by simp [gen]
    have h3 : (Finsupp.single i (1 : ℤ)) j = 0 := Finsupp.single_eq_of_ne (Ne.symm hij)
    rw [h1, h2, h3]
    simp

theorem chi_gen (q : M → ℂ) (i : M) : chi q (gen i) = q i := by
  rw [chi, charge_gen, zprod,
    Finsupp.prod_single_index (h := fun j k => q j ^ k) (zpow_zero (q i)), zpow_one]

/-- **The flow scales the isometry of mode `i` by `q i`.**  This is the eigenvalue hypothesis the
KMS exchange lemmas need. -/
theorem twist_gasV (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (i : M) :
    twist q hq (gasV i) = q i • gasV i := by
  rw [gasV, twist_single, chi_gen, one_mul, MonoidAlgebra.smul_single', mul_one]

end GaloisForLFunctions.HTGeometry
