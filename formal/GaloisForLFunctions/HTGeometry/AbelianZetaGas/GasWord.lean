import Mathlib

/-!
# The monomial monoid of the multi-mode Toeplitz gas

A monomial of the gas algebra is a product `∏_i V_i^{a_i} (V_i^*)^{b_i}` over finitely many modes,
where each `V_i` is an isometry: `V_i^* V_i = 1`.  Multiplying two such monomials contracts the
inner block through `(V^*)^b V^{b'} = (V^*)^{b - b'} V^{b' - b}`, which is exactly the bicyclic
monoid law, applied mode by mode.  This file builds that monoid: a word is a pair of finitely
supported exponent families, and the product is the pointwise bicyclic product.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A monomial of the gas algebra: `∏_i V_i^{raise i} (V_i^*)^{lower i}`. -/
@[ext]
structure GasWord (M : Type*) where
  /-- The exponents of the isometries. -/
  raise : M →₀ ℕ
  /-- The exponents of their adjoints. -/
  lower : M →₀ ℕ

namespace GasWord

variable {M : Type*}

instance : One (GasWord M) := ⟨⟨0, 0⟩⟩

noncomputable instance : Mul (GasWord M) :=
  ⟨fun x y => ⟨x.raise + (y.raise - x.lower), y.lower + (x.lower - y.raise)⟩⟩

@[simp] theorem one_raise : (1 : GasWord M).raise = 0 := rfl

@[simp] theorem one_lower : (1 : GasWord M).lower = 0 := rfl

@[simp] theorem mul_raise (x y : GasWord M) :
    (x * y).raise = x.raise + (y.raise - x.lower) := rfl

@[simp] theorem mul_lower (x y : GasWord M) :
    (x * y).lower = y.lower + (x.lower - y.raise) := rfl

theorem raise_apply_mul (x y : GasWord M) (i : M) :
    (x * y).raise i = x.raise i + (y.raise i - x.lower i) := by
  rw [mul_raise, Finsupp.add_apply, Finsupp.tsub_apply]

theorem lower_apply_mul (x y : GasWord M) (i : M) :
    (x * y).lower i = y.lower i + (x.lower i - y.raise i) := by
  rw [mul_lower, Finsupp.add_apply, Finsupp.tsub_apply]

noncomputable instance : Monoid (GasWord M) where
  mul_assoc x y z := by
    refine GasWord.ext ?_ ?_ <;> refine Finsupp.ext fun i => ?_
    · rw [raise_apply_mul, raise_apply_mul, raise_apply_mul, lower_apply_mul,
        raise_apply_mul]
      omega
    · rw [lower_apply_mul, lower_apply_mul, lower_apply_mul, raise_apply_mul,
        lower_apply_mul]
      omega
  one_mul x := by
    refine GasWord.ext ?_ ?_ <;> refine Finsupp.ext fun i => ?_
    · rw [raise_apply_mul]
      simp
    · rw [lower_apply_mul]
      simp
  mul_one x := by
    refine GasWord.ext ?_ ?_ <;> refine Finsupp.ext fun i => ?_
    · rw [raise_apply_mul]
      simp
    · rw [lower_apply_mul]
      simp

/-! ## Generators, blocks, and the disjoint-mode commutation -/

/-- The isometry of mode `i`. -/
noncomputable def gen (i : M) : GasWord M := ⟨Finsupp.single i 1, 0⟩

/-- The adjoint of the isometry of mode `i`. -/
noncomputable def cogen (i : M) : GasWord M := ⟨0, Finsupp.single i 1⟩

/-- The one-mode block `V_i^a (V_i^*)^b`. -/
noncomputable def block (i : M) (a b : ℕ) : GasWord M :=
  ⟨Finsupp.single i a, Finsupp.single i b⟩

/-- The word with mode `i` removed. -/
noncomputable def erase (i : M) (x : GasWord M) : GasWord M :=
  ⟨x.raise.erase i, x.lower.erase i⟩

@[simp] theorem erase_raise (i : M) (x : GasWord M) :
    (erase i x).raise = x.raise.erase i := rfl

@[simp] theorem erase_lower (i : M) (x : GasWord M) :
    (erase i x).lower = x.lower.erase i := rfl

theorem mk_eq_mul (a b : M →₀ ℕ) :
    (⟨a, b⟩ : GasWord M) = (⟨a, 0⟩ : GasWord M) * (⟨0, b⟩ : GasWord M) := by
  refine GasWord.ext ?_ ?_ <;> refine Finsupp.ext fun i => ?_
  · rw [raise_apply_mul]; simp
  · rw [lower_apply_mul]; simp

/-- **The isometry relation** `V_i^* V_i = 1`. -/
theorem cogen_mul_gen (i : M) : cogen i * gen i = 1 := by
  refine GasWord.ext ?_ ?_ <;> refine Finsupp.ext fun j => ?_
  · rw [raise_apply_mul]; simp [cogen, gen]
  · rw [lower_apply_mul]; simp [cogen, gen]

theorem gen_pow (i : M) (n : ℕ) : gen i ^ n = ⟨Finsupp.single i n, 0⟩ := by
  induction n with
  | zero => refine GasWord.ext ?_ ?_ <;> simp [gen]
  | succ m ih =>
    rw [pow_succ, ih]
    refine GasWord.ext ?_ ?_ <;> refine Finsupp.ext fun j => ?_
    · rw [raise_apply_mul]
      by_cases hij : i = j
      · subst hij
        simp [gen]
      · simp only [gen, Finsupp.single_apply, if_neg hij, Finsupp.coe_zero, Pi.zero_apply]
        omega
    · rw [lower_apply_mul]
      simp [gen]

theorem cogen_pow (i : M) (n : ℕ) : cogen i ^ n = ⟨0, Finsupp.single i n⟩ := by
  induction n with
  | zero => refine GasWord.ext ?_ ?_ <;> simp [cogen]
  | succ m ih =>
    rw [pow_succ, ih]
    refine GasWord.ext ?_ ?_ <;> refine Finsupp.ext fun j => ?_
    · rw [raise_apply_mul]
      simp [cogen]
    · rw [lower_apply_mul]
      by_cases hij : i = j
      · subst hij
        simp only [cogen, Finsupp.single_eq_same, Finsupp.coe_zero, Pi.zero_apply,
          Nat.sub_zero]
        omega
      · simp only [cogen, Finsupp.single_apply, if_neg hij, Finsupp.coe_zero, Pi.zero_apply]
        omega

theorem block_eq (i : M) (a b : ℕ) : block i a b = gen i ^ a * cogen i ^ b := by
  rw [gen_pow, cogen_pow, block]
  exact mk_eq_mul _ _

/-- **Words supported on disjoint mode sets commute.** -/
theorem mul_comm_of_disjoint {x y : GasWord M}
    (h : ∀ i, (x.raise i = 0 ∧ x.lower i = 0) ∨ (y.raise i = 0 ∧ y.lower i = 0)) :
    x * y = y * x := by
  refine GasWord.ext ?_ ?_ <;> refine Finsupp.ext fun i => ?_
  · rw [raise_apply_mul, raise_apply_mul]
    rcases h i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> omega
  · rw [lower_apply_mul, lower_apply_mul]
    rcases h i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> omega

/-- **Peeling one mode off a word.** -/
theorem eq_block_mul_erase (i : M) (x : GasWord M) :
    x = block i (x.raise i) (x.lower i) * erase i x := by
  refine GasWord.ext ?_ ?_ <;> refine Finsupp.ext fun j => ?_
  · rw [raise_apply_mul]
    by_cases hij : j = i
    · subst hij
      simp [block]
    · simp [block, Finsupp.single_apply, hij, Finsupp.erase_ne hij]
  · rw [lower_apply_mul]
    by_cases hij : j = i
    · subst hij
      simp [block]
    · simp [block, Finsupp.single_apply, hij, Finsupp.erase_ne hij]

theorem disjoint_block_erase (i : M) (x y : GasWord M) :
    ∀ j, ((block i (x.raise i) (x.lower i)).raise j = 0
        ∧ (block i (x.raise i) (x.lower i)).lower j = 0)
      ∨ ((erase i y).raise j = 0 ∧ (erase i y).lower j = 0) := by
  intro j
  by_cases hij : j = i
  · subst hij
    exact Or.inr ⟨by simp, by simp⟩
  · exact Or.inl ⟨by simp [block, Finsupp.single_apply, hij],
      by simp [block, Finsupp.single_apply, hij]⟩

/-! ## The charge -/

/-- The charge of a word: `raise − lower`, read in `ℤ`. -/
noncomputable def charge (x : GasWord M) : M →₀ ℤ :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) x.raise
    - Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) x.lower

theorem charge_apply (x : GasWord M) (i : M) :
    charge x i = (x.raise i : ℤ) - (x.lower i : ℤ) := by
  rw [charge, Finsupp.sub_apply, Finsupp.mapRange_apply, Finsupp.mapRange_apply]

/-- **The charge is additive.** -/
theorem charge_mul (x y : GasWord M) : charge (x * y) = charge x + charge y := by
  refine Finsupp.ext fun i => ?_
  rw [charge_apply, Finsupp.add_apply, charge_apply, charge_apply,
    raise_apply_mul, lower_apply_mul]
  push_cast
  omega

@[simp] theorem charge_one : charge (1 : GasWord M) = 0 := by
  refine Finsupp.ext fun i => ?_
  rw [charge_apply]
  simp

/-- A word is diagonal exactly when it has zero charge. -/
theorem charge_eq_zero_iff (x : GasWord M) : charge x = 0 ↔ x.raise = x.lower := by
  constructor
  · intro h
    refine Finsupp.ext fun i => ?_
    have := congrFun (congrArg (fun f : M →₀ ℤ => (f : M → ℤ)) h) i
    rw [charge_apply] at this
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  · intro h
    refine Finsupp.ext fun i => ?_
    rw [charge_apply, h]
    simp

end GasWord

end GaloisForLFunctions.HTGeometry
