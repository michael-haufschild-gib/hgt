import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# The Ore ring of linear differential operators

For a commutative differential ring `K` with derivation `a ↦ a′`, the linear differential
operators

`p = ∑ₙ aₙ ∂ⁿ`

form an associative unital ring in which scalars do not commute with `∂`:

`∂ · a = a · ∂ + a′`.

This file constructs that ring as the finitely supported coefficient families `ℕ →₀ K`.
Multiplication is defined by iterating the additive map `dpartial` of left multiplication by
`∂`, which avoids all binomial bookkeeping: associativity follows from the two identities

`dpartial (a • p) = a • dpartial p + a′ • p`,  `dpartial p * q = dpartial (p * q)`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

universe u

/-- Linear differential operators `∑ₙ aₙ ∂ⁿ` over a commutative differential ring `K`,
represented by their finitely supported coefficient families. -/
def DiffOp (K : Type u) [CommRing K] [Differential K] : Type u := ℕ →₀ K

namespace DiffOp

noncomputable section

variable {K : Type u} [CommRing K] [Differential K]

instance instAddCommGroup : AddCommGroup (DiffOp K) := inferInstanceAs (AddCommGroup (ℕ →₀ K))

instance : Module K (DiffOp K) := inferInstanceAs (Module K (ℕ →₀ K))

instance : Inhabited (DiffOp K) := ⟨(0 : ℕ →₀ K)⟩

/-- The coefficient family of an operator. -/
def toFinsupp (p : DiffOp K) : ℕ →₀ K := p

/-- The operator with a prescribed coefficient family. -/
def ofFinsupp (p : ℕ →₀ K) : DiffOp K := p

@[simp] theorem toFinsupp_ofFinsupp (p : ℕ →₀ K) : toFinsupp (ofFinsupp p) = p := rfl

@[simp] theorem ofFinsupp_toFinsupp (p : DiffOp K) : ofFinsupp (toFinsupp p) = p := rfl

@[simp] theorem toFinsupp_zero : toFinsupp (0 : DiffOp K) = 0 := rfl

@[simp] theorem toFinsupp_add (p q : DiffOp K) :
    toFinsupp (p + q) = toFinsupp p + toFinsupp q := rfl

@[simp] theorem toFinsupp_neg (p : DiffOp K) : toFinsupp (-p) = -toFinsupp p := rfl

@[simp] theorem toFinsupp_sub (p q : DiffOp K) :
    toFinsupp (p - q) = toFinsupp p - toFinsupp q := rfl

@[simp] theorem toFinsupp_smul (a : K) (p : DiffOp K) :
    toFinsupp (a • p) = a • toFinsupp p := rfl

/-- The coefficient of `∂ⁿ`. -/
def coeff (p : DiffOp K) (n : ℕ) : K := toFinsupp p n

@[ext]
theorem ext {p q : DiffOp K} (h : ∀ n, coeff p n = coeff q n) : p = q := by
  have hfs : toFinsupp p = toFinsupp q := Finsupp.ext h
  exact hfs

@[simp] theorem coeff_zero (n : ℕ) : coeff (0 : DiffOp K) n = 0 := rfl

@[simp] theorem coeff_add (p q : DiffOp K) (n : ℕ) :
    coeff (p + q) n = coeff p n + coeff q n := by
  simp [coeff]

@[simp] theorem coeff_neg (p : DiffOp K) (n : ℕ) : coeff (-p) n = -coeff p n := by
  simp [coeff]

@[simp] theorem coeff_sub (p q : DiffOp K) (n : ℕ) :
    coeff (p - q) n = coeff p n - coeff q n := by
  simp [coeff]

@[simp] theorem coeff_smul (a : K) (p : DiffOp K) (n : ℕ) :
    coeff (a • p) n = a * coeff p n := by
  simp [coeff]

theorem eq_zero_iff {p : DiffOp K} : p = 0 ↔ ∀ n, coeff p n = 0 :=
  ⟨fun h n => by rw [h, coeff_zero], fun h => ext fun n => by rw [h n, coeff_zero]⟩

/-- The monomial operator `a ∂ⁿ`. -/
def mono (n : ℕ) (a : K) : DiffOp K := ofFinsupp (Finsupp.single n a)

@[simp] theorem toFinsupp_mono (n : ℕ) (a : K) :
    toFinsupp (mono n a) = Finsupp.single n a := rfl

theorem coeff_mono (n m : ℕ) (a : K) :
    coeff (mono n a) m = if n = m then a else 0 := Finsupp.single_apply

@[simp] theorem coeff_mono_self (n : ℕ) (a : K) : coeff (mono n a) n = a := by
  simp [coeff_mono]

theorem coeff_mono_of_ne {n m : ℕ} (a : K) (h : n ≠ m) : coeff (mono n a) m = 0 := by
  simp [coeff_mono, h]

@[simp] theorem mono_zero (n : ℕ) : mono n (0 : K) = 0 := by
  ext m
  by_cases h : n = m <;> simp [coeff_mono, h]

theorem mono_add (n : ℕ) (a b : K) : mono n (a + b) = mono n a + mono n b := by
  ext m
  by_cases h : n = m <;> simp [coeff_mono, h]

theorem smul_mono (a b : K) (n : ℕ) : a • mono n b = mono n (a * b) := by
  ext m
  by_cases h : n = m <;> simp [coeff_mono, h]

/-- Additive induction on operators through monomials. -/
theorem induction_linear {motive : DiffOp K → Prop} (p : DiffOp K) (h0 : motive 0)
    (hadd : ∀ p q, motive p → motive q → motive (p + q))
    (hmono : ∀ n a, motive (mono n a)) : motive p :=
  Finsupp.induction_linear (motive := fun f : ℕ →₀ K => motive (ofFinsupp f)) (toFinsupp p) h0
    (fun f g hf hg => hadd (ofFinsupp f) (ofFinsupp g) hf hg) (fun n a => hmono n a)

/-- The derivation of `K` as an additive homomorphism. -/
def derivAddHom (K : Type u) [CommRing K] [Differential K] : K →+ K :=
  (Differential.deriv : Derivation ℤ K K).toLinearMap.toAddMonoidHom

@[simp] theorem derivAddHom_apply (a : K) : derivAddHom K a = a′ := rfl

/-- Left multiplication by `∂`: `∂ · ∑ aₙ ∂ⁿ = ∑ aₙ ∂ⁿ⁺¹ + ∑ aₙ′ ∂ⁿ`. -/
def dpartial (p : DiffOp K) : DiffOp K :=
  ofFinsupp (Finsupp.mapDomain Nat.succ (toFinsupp p) +
    Finsupp.mapRange (derivAddHom K) (map_zero _) (toFinsupp p))

theorem coeff_dpartial_zero (p : DiffOp K) : coeff (dpartial p) 0 = (coeff p 0)′ := by
  have h : ((0 : ℕ) ∉ Set.range Nat.succ) := by
    rintro ⟨m, hm⟩
    exact Nat.succ_ne_zero m hm
  show (Finsupp.mapDomain Nat.succ (toFinsupp p)) 0 +
      (Finsupp.mapRange (derivAddHom K) (map_zero _) (toFinsupp p)) 0 = _
  rw [Finsupp.mapDomain_notin_range _ _ h, Finsupp.mapRange_apply]
  simp [coeff]

theorem coeff_dpartial_succ (p : DiffOp K) (n : ℕ) :
    coeff (dpartial p) (n + 1) = coeff p n + (coeff p (n + 1))′ := by
  show (Finsupp.mapDomain Nat.succ (toFinsupp p)) (Nat.succ n) +
      (Finsupp.mapRange (derivAddHom K) (map_zero _) (toFinsupp p)) (n + 1) = _
  rw [Finsupp.mapDomain_apply Nat.succ_injective, Finsupp.mapRange_apply]
  simp [coeff]

@[simp] theorem dpartial_add (p q : DiffOp K) :
    dpartial (p + q) = dpartial p + dpartial q := by
  ext n
  cases n with
  | zero => simp [coeff_dpartial_zero]
  | succ n =>
    simp only [coeff_dpartial_succ, coeff_add]
    rw [map_add]
    ring

@[simp] theorem dpartial_zero : dpartial (0 : DiffOp K) = 0 := by
  ext n
  cases n with
  | zero => simp [coeff_dpartial_zero]
  | succ n => simp [coeff_dpartial_succ]

theorem dpartial_mono (n : ℕ) (a : K) :
    dpartial (mono n a) = mono (n + 1) a + mono n a′ := by
  ext m
  cases m with
  | zero =>
    rw [coeff_dpartial_zero]
    by_cases h : n = 0
    · subst h; simp [coeff_mono]
    · simp [coeff_mono, h]
  | succ m =>
    rw [coeff_dpartial_succ]
    by_cases h : n = m
    · subst h
      simp [coeff_mono]
    · by_cases h' : n = m + 1
      · subst h'
        simp [coeff_mono]
      · simp [coeff_mono, h, h']

/-- The Leibniz rule for left multiplication by `∂`. -/
theorem dpartial_smul (a : K) (p : DiffOp K) :
    dpartial (a • p) = a • dpartial p + a′ • p := by
  ext n
  cases n with
  | zero =>
    simp only [coeff_dpartial_zero, coeff_smul, coeff_add]
    rw [Derivation.leibniz]
    simp [mul_comm]
  | succ n =>
    simp only [coeff_dpartial_succ, coeff_smul, coeff_add]
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring

theorem dpartial_iterate_add (n : ℕ) (q r : DiffOp K) :
    dpartial^[n] (q + r) = dpartial^[n] q + dpartial^[n] r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, dpartial_add]

theorem dpartial_iterate_zero (n : ℕ) : dpartial^[n] (0 : DiffOp K) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, dpartial_zero]

/-- The additive homomorphism `a ↦ a • ∂ⁿ q`. -/
def mulAux (q : DiffOp K) (n : ℕ) : K →+ DiffOp K where
  toFun a := a • (dpartial^[n] q)
  map_zero' := zero_smul _ _
  map_add' a b := add_smul a b _

instance : Mul (DiffOp K) := ⟨fun p q => Finsupp.liftAddHom (mulAux q) (toFinsupp p)⟩

instance : One (DiffOp K) := ⟨mono 0 1⟩

theorem one_def : (1 : DiffOp K) = mono 0 1 := rfl

theorem mul_def (p q : DiffOp K) :
    p * q = Finsupp.liftAddHom (mulAux q) (toFinsupp p) := rfl

theorem mono_mul (n : ℕ) (a : K) (q : DiffOp K) :
    mono n a * q = a • (dpartial^[n] q) := by
  rw [mul_def, toFinsupp_mono]
  exact Finsupp.liftAddHom_apply_single (mulAux q) n a

@[simp] theorem zero_mul' (q : DiffOp K) : (0 : DiffOp K) * q = 0 := by
  rw [mul_def, toFinsupp_zero, map_zero]

theorem add_mul' (p₁ p₂ q : DiffOp K) : (p₁ + p₂) * q = p₁ * q + p₂ * q := by
  simp only [mul_def, toFinsupp_add, map_add]

@[simp] theorem mul_zero' (p : DiffOp K) : p * (0 : DiffOp K) = 0 := by
  refine induction_linear (motive := fun p => p * (0 : DiffOp K) = 0) p ?_ ?_ ?_
  · exact zero_mul' _
  · intro p q hp hq
    rw [add_mul', hp, hq, add_zero]
  · intro n a
    rw [mono_mul, dpartial_iterate_zero, smul_zero]

theorem mul_add' (p q r : DiffOp K) : p * (q + r) = p * q + p * r := by
  refine induction_linear (motive := fun p => p * (q + r) = p * q + p * r) p ?_ ?_ ?_
  · simp
  · intro p₁ p₂ h₁ h₂
    rw [add_mul', h₁, h₂, add_mul', add_mul']
    abel
  · intro n a
    rw [mono_mul, mono_mul, mono_mul, dpartial_iterate_add, smul_add]

theorem smul_mul' (a : K) (p q : DiffOp K) : (a • p) * q = a • (p * q) := by
  refine induction_linear (motive := fun p => (a • p) * q = a • (p * q)) p ?_ ?_ ?_
  · simp
  · intro p₁ p₂ h₁ h₂
    rw [smul_add, add_mul', h₁, h₂, add_mul', smul_add]
  · intro n b
    rw [smul_mono, mono_mul, mono_mul, smul_smul]

/-- Left multiplication by `∂` is left multiplication by the operator `∂`. -/
theorem dpartial_mul (p q : DiffOp K) : (dpartial p) * q = dpartial (p * q) := by
  refine induction_linear (motive := fun p => (dpartial p) * q = dpartial (p * q)) p ?_ ?_ ?_
  · simp
  · intro p₁ p₂ h₁ h₂
    rw [dpartial_add, add_mul', h₁, h₂, add_mul', dpartial_add]
  · intro n a
    rw [dpartial_mono, add_mul', mono_mul, mono_mul, mono_mul, dpartial_smul,
      Function.iterate_succ_apply']

theorem dpartial_iterate_mul (n : ℕ) (p q : DiffOp K) :
    (dpartial^[n] p) * q = dpartial^[n] (p * q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dpartial_mul, ih]

theorem mul_assoc' (p q r : DiffOp K) : (p * q) * r = p * (q * r) := by
  refine induction_linear (motive := fun p => (p * q) * r = p * (q * r)) p ?_ ?_ ?_
  · simp
  · intro p₁ p₂ h₁ h₂
    rw [add_mul', add_mul', h₁, h₂, add_mul']
  · intro n a
    rw [mono_mul, smul_mul', dpartial_iterate_mul, mono_mul]

theorem dpartial_iterate_one (n : ℕ) : dpartial^[n] (1 : DiffOp K) = mono n 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, dpartial_mono]
    simp

theorem one_mul' (q : DiffOp K) : (1 : DiffOp K) * q = q := by
  rw [one_def, mono_mul]
  simp

theorem mul_one' (p : DiffOp K) : p * (1 : DiffOp K) = p := by
  refine induction_linear (motive := fun p => p * (1 : DiffOp K) = p) p ?_ ?_ ?_
  · simp
  · intro p₁ p₂ h₁ h₂
    rw [add_mul', h₁, h₂]
  · intro n a
    rw [mono_mul, dpartial_iterate_one, smul_mono, mul_one]

instance : Ring (DiffOp K) :=
  let acg : AddCommGroup (DiffOp K) := instAddCommGroup
  { acg with
    mul := (· * ·)
    one := 1
    left_distrib := mul_add'
    right_distrib := add_mul'
    zero_mul := zero_mul'
    mul_zero := mul_zero'
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := mul_one' }

instance : IsScalarTower K (DiffOp K) (DiffOp K) :=
  ⟨fun a p q => smul_mul' a p q⟩

/-- Scalars, as order-zero operators. -/
def C (a : K) : DiffOp K := mono 0 a

@[simp] theorem C_apply (a : K) : C a = mono 0 a := rfl

theorem C_mul (a : K) (p : DiffOp K) : C a * p = a • p := by
  rw [C_apply, mono_mul]
  rfl

/-- The operator `∂`. -/
def X : DiffOp K := mono 1 1

theorem X_mul (p : DiffOp K) : (X : DiffOp K) * p = dpartial p := by
  rw [X, mono_mul]
  simp

theorem X_pow_mul (n : ℕ) (p : DiffOp K) : (X : DiffOp K) ^ n * p = dpartial^[n] p := by
  induction n generalizing p with
  | zero => rw [pow_zero, one_mul']; rfl
  | succ n ih =>
    rw [pow_succ, mul_assoc', X_mul, ih, Function.iterate_succ_apply]

theorem X_pow_eq_mono (n : ℕ) : (X : DiffOp K) ^ n = mono n 1 := by
  rw [← mul_one' ((X : DiffOp K) ^ n), X_pow_mul, dpartial_iterate_one]

theorem mono_eq_C_mul_X_pow (n : ℕ) (a : K) :
    mono n a = C a * (X : DiffOp K) ^ n := by
  rw [C_mul, X_pow_eq_mono, smul_mono, mul_one]

end

end DiffOp

namespace DiffOp

noncomputable section

variable {K : Type u} [CommRing K] [Differential K]

/-- Coefficient extraction, as an additive homomorphism. -/
def coeffAddHom (n : ℕ) : DiffOp K →+ K where
  toFun p := coeff p n
  map_zero' := coeff_zero n
  map_add' p q := coeff_add p q n

@[simp] theorem coeffAddHom_apply (n : ℕ) (p : DiffOp K) : coeffAddHom n p = coeff p n := rfl

theorem mul_eq_sum (p q : DiffOp K) :
    p * q = ∑ n ∈ (toFinsupp p).support, coeff p n • dpartial^[n] q := by
  rw [mul_def, Finsupp.liftAddHom_apply]
  rfl

theorem coeff_mul (p q : DiffOp K) (N : ℕ) :
    coeff (p * q) N = ∑ n ∈ (toFinsupp p).support, coeff p n * coeff (dpartial^[n] q) N := by
  rw [mul_eq_sum]
  rw [← coeffAddHom_apply N, map_sum]
  simp

/-- The order of an operator.  The zero operator is given order `0`, so that `degree` is the
truncated order `max (0, ord)` used in two-sided comparison estimates. -/
def degree (p : DiffOp K) : ℕ := (toFinsupp p).support.sup id

theorem degree_le_iff {p : DiffOp K} {n : ℕ} :
    degree p ≤ n ↔ ∀ m, n < m → coeff p m = 0 := by
  constructor
  · intro h m hm
    by_contra hc
    have hmem : m ∈ (toFinsupp p).support := Finsupp.mem_support_iff.mpr hc
    have : m ≤ degree p := Finset.le_sup (f := id) hmem
    omega
  · intro h
    refine Finset.sup_le ?_
    intro m hm
    by_contra hc
    exact (Finsupp.mem_support_iff.mp hm) (h m (by simpa using Nat.lt_of_not_le hc))

theorem coeff_eq_zero_of_degree_lt {p : DiffOp K} {n : ℕ} (h : degree p < n) :
    coeff p n = 0 :=
  degree_le_iff.mp le_rfl n h

theorem le_degree {p : DiffOp K} {n : ℕ} (h : coeff p n ≠ 0) : n ≤ degree p :=
  Finset.le_sup (f := id) (Finsupp.mem_support_iff.mpr h)

/-- The leading coefficient of an operator. -/
def leadCoeff (p : DiffOp K) : K := coeff p (degree p)

theorem leadCoeff_ne_zero {p : DiffOp K} (hp : p ≠ 0) : leadCoeff p ≠ 0 := by
  have hne : (toFinsupp p).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h
    exact hp h
  have hmem : degree p ∈ (toFinsupp p).support := by
    have hmm := Finset.max'_mem (toFinsupp p).support hne
    have hmax : (toFinsupp p).support.max' hne = degree p := by
      rw [degree, Finset.max'_eq_sup', Finset.sup'_eq_sup]
    rwa [hmax] at hmm
  exact Finsupp.mem_support_iff.mp hmem

@[simp] theorem degree_zero : degree (0 : DiffOp K) = 0 := by
  simp [degree]

theorem degree_mono_le (n : ℕ) (a : K) : degree (mono n a) ≤ n := by
  refine degree_le_iff.mpr ?_
  intro m hm
  exact coeff_mono_of_ne a (by omega)

theorem degree_add_le (p q : DiffOp K) :
    degree (p + q) ≤ max (degree p) (degree q) := by
  refine degree_le_iff.mpr ?_
  intro m hm
  rw [coeff_add, coeff_eq_zero_of_degree_lt (lt_of_le_of_lt (le_max_left _ _) hm),
    coeff_eq_zero_of_degree_lt (lt_of_le_of_lt (le_max_right _ _) hm), add_zero]

theorem degree_neg (p : DiffOp K) : degree (-p) = degree p := by
  refine le_antisymm (degree_le_iff.mpr fun m hm => ?_) (degree_le_iff.mpr fun m hm => ?_)
  · rw [coeff_neg, coeff_eq_zero_of_degree_lt hm, neg_zero]
  · have h := coeff_eq_zero_of_degree_lt (p := -p) hm
    rw [coeff_neg, neg_eq_zero] at h
    exact h

theorem degree_sub_le (p q : DiffOp K) :
    degree (p - q) ≤ max (degree p) (degree q) := by
  rw [sub_eq_add_neg]
  refine le_trans (degree_add_le p (-q)) ?_
  rw [degree_neg]

theorem degree_smul_le (a : K) (p : DiffOp K) : degree (a • p) ≤ degree p := by
  refine degree_le_iff.mpr ?_
  intro m hm
  rw [coeff_smul, coeff_eq_zero_of_degree_lt hm, mul_zero]

theorem degree_dpartial_le (p : DiffOp K) : degree (dpartial p) ≤ degree p + 1 := by
  refine degree_le_iff.mpr ?_
  intro m hm
  cases m with
  | zero => omega
  | succ m =>
    rw [coeff_dpartial_succ, coeff_eq_zero_of_degree_lt (by omega),
      coeff_eq_zero_of_degree_lt (by omega)]
    simp

theorem degree_dpartial_iterate_le (n : ℕ) (p : DiffOp K) :
    degree (dpartial^[n] p) ≤ degree p + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact le_trans (degree_dpartial_le _) (by omega)

theorem coeff_dpartial_iterate_top (n : ℕ) (q : DiffOp K) :
    coeff (dpartial^[n] q) (degree q + n) = leadCoeff q := by
  induction n with
  | zero => simp [leadCoeff]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hzero : coeff (dpartial^[n] q) (degree q + n + 1) = 0 :=
      coeff_eq_zero_of_degree_lt
        (lt_of_le_of_lt (degree_dpartial_iterate_le n q) (by omega))
    have hidx : degree q + (n + 1) = (degree q + n) + 1 := by omega
    rw [hidx, coeff_dpartial_succ, ih, hzero]
    simp

theorem degree_mul_le (p q : DiffOp K) : degree (p * q) ≤ degree p + degree q := by
  refine degree_le_iff.mpr ?_
  intro N hN
  rw [coeff_mul]
  refine Finset.sum_eq_zero ?_
  intro n hn
  have hnle : n ≤ degree p := Finset.le_sup (f := id) hn
  have hlt : degree (dpartial^[n] q) < N :=
    lt_of_le_of_lt (degree_dpartial_iterate_le n q) (by omega)
  rw [coeff_eq_zero_of_degree_lt hlt, mul_zero]

theorem coeff_mul_top (p q : DiffOp K) :
    coeff (p * q) (degree p + degree q) = leadCoeff p * leadCoeff q := by
  by_cases hp : p = 0
  · subst hp
    simp [leadCoeff]
  have hmem : degree p ∈ (toFinsupp p).support :=
    Finsupp.mem_support_iff.mpr (leadCoeff_ne_zero hp)
  rw [coeff_mul]
  refine (Finset.sum_eq_single_of_mem (degree p) hmem ?_).trans ?_
  · intro n hn hne'
    have hnle : n ≤ degree p := Finset.le_sup (f := id) hn
    have hlt : degree (dpartial^[n] q) < degree p + degree q :=
      lt_of_le_of_lt (degree_dpartial_iterate_le n q) (by omega)
    rw [coeff_eq_zero_of_degree_lt hlt, mul_zero]
  · have hcomm : degree p + degree q = degree q + degree p := by omega
    rw [hcomm, coeff_dpartial_iterate_top]
    rfl

section Domain

variable [NoZeroDivisors K]

theorem leadCoeff_mul_and_degree_mul {p q : DiffOp K} (hp : p ≠ 0) (hq : q ≠ 0) :
    leadCoeff (p * q) = leadCoeff p * leadCoeff q ∧ degree (p * q) = degree p + degree q := by
  have htop : coeff (p * q) (degree p + degree q) = leadCoeff p * leadCoeff q :=
    coeff_mul_top p q
  have hne : leadCoeff p * leadCoeff q ≠ 0 :=
    mul_ne_zero (leadCoeff_ne_zero hp) (leadCoeff_ne_zero hq)
  have hdeg : degree (p * q) = degree p + degree q :=
    le_antisymm (degree_mul_le p q) (le_degree (by rw [htop]; exact hne))
  exact ⟨by rw [leadCoeff, hdeg, htop], hdeg⟩

theorem degree_mul {p q : DiffOp K} (hp : p ≠ 0) (hq : q ≠ 0) :
    degree (p * q) = degree p + degree q := (leadCoeff_mul_and_degree_mul hp hq).2

theorem leadCoeff_mul {p q : DiffOp K} (hp : p ≠ 0) (hq : q ≠ 0) :
    leadCoeff (p * q) = leadCoeff p * leadCoeff q := (leadCoeff_mul_and_degree_mul hp hq).1

theorem mul_ne_zero' {p q : DiffOp K} (hp : p ≠ 0) (hq : q ≠ 0) : p * q ≠ 0 := by
  intro h
  have hlead := (leadCoeff_mul_and_degree_mul hp hq).1
  rw [h] at hlead
  simp only [leadCoeff, coeff_zero] at hlead
  exact (mul_ne_zero (leadCoeff_ne_zero hp) (leadCoeff_ne_zero hq)) hlead.symm

instance : NoZeroDivisors (DiffOp K) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    by_contra hc
    exact mul_ne_zero' (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h)) hab

end Domain

instance [Nontrivial K] : Nontrivial (DiffOp K) where
  exists_pair_ne := by
    refine ⟨0, 1, ?_⟩
    intro h
    have hc := congrArg (fun p => coeff p 0) h
    simp [one_def] at hc

end

end DiffOp

end GaloisForLFunctions.HTGeometry
