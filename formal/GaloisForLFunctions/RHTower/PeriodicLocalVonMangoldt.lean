import Mathlib

/-!
# The local von Mangoldt sequence of a periodic Dirichlet coefficient

Let `N` be a polynomial with `N.natDegree < d`, and let

`a k = N.coeff (k % d)`

be the `d`-periodic extension of its coefficient sequence.  The generating function of `a` is
`∑ a k X ^ k = N X / (1 - X ^ d)`.

For a Dirichlet series `F s = ∑ α n * n ^ (-s)` with `α` periodic modulo `q` and `α 1 = 1`, and a
prime `p` not dividing `q` of multiplicative order `d` modulo `q`, the sequence `i ↦ α (p ^ i)` is
exactly such an `a`, with `N X = ∑_{i < d} α (p ^ i) X ^ i`.  The coefficients of `-F' / F` at the
powers of `p` are then `b (p ^ k) = Λ k * log p`, where `Λ` is the *local von Mangoldt sequence*
of `a`: the unique sequence satisfying

`∑_{j = 1}^{k} Λ j * a (k - j) = k * a k`,

the coefficient sequence of `X * G' / G` for `G` the generating function of `a`.

The main theorem `isLocalVonMangoldt_iff_isRecipPowerSum` says that `Λ` decomposes as

`Λ k = d * [d ∣ k] - π k`,

where `π` is attached to `N` alone by

`∑_{j = 1}^{k} π j * N.coeff (k - j) = -k * N.coeff k`,

the coefficient sequence of `-X * N' / N`; equivalently `π k` is the `k`-th power sum of the
reciprocal roots of `N`.  So the local von Mangoldt data of a periodic coefficient splits into a
universal cyclotomic term depending only on the period and the reciprocal-root power sums of the
finite local polynomial.

Two consequences are recorded.  `geometric_vonMangoldt_iff` shows that a local sequence is an Euler
factor — `a k = c ^ k` — exactly when its local von Mangoldt sequence is `Λ k = c ^ k`; with
`periodicCoeff_geometric_iff` this identifies having an Euler factor with `N` being the cyclotomic
quotient `(1 - X ^ d) / (1 - c X)`, that is, with the reciprocal roots of `N` being the `d`-th roots
of unity other than `c`.  `periodic_of_periodic_recipPowerSum` shows that a periodic `π` forces a
periodic, hence finite-valued, `Λ`.
-/

open Finset

namespace RHTower

noncomputable section

/-- The `d`-periodic extension of the coefficient sequence of a polynomial `N`.
Its generating series is `N X / (1 - X ^ d)` when `N.natDegree < d`. -/
def periodicCoeff (N : Polynomial ℂ) (d k : ℕ) : ℂ := N.coeff (k % d)

/-- The universal cyclotomic term `d * [d ∣ k]`: the local von Mangoldt data of the constant
periodic sequence of period `d`. -/
def cycloTerm (d k : ℕ) : ℂ := if d ∣ k then (d : ℂ) else 0

/-- `Λ` is the local von Mangoldt sequence of the `d`-periodic coefficient attached to `N`, i.e.
the coefficient sequence of `X * G' / G` for `G` the generating function of that coefficient. -/
def IsLocalVonMangoldt (N : Polynomial ℂ) (d : ℕ) (Λ : ℕ → ℂ) : Prop :=
  ∀ k, 0 < k → ∑ j ∈ Ioc 0 k, Λ j * periodicCoeff N d (k - j) = (k : ℂ) * periodicCoeff N d k

/-- `π` is the reciprocal-root power sum sequence of `N`, i.e. the coefficient sequence of
`-X * N' / N`.  For `N = ∏ (1 - y i * X)` this says `π k = ∑ y i ^ k`. -/
def IsRecipPowerSum (N : Polynomial ℂ) (π : ℕ → ℂ) : Prop :=
  ∀ k, 0 < k → ∑ j ∈ Ioc 0 k, π j * N.coeff (k - j) = -(k : ℂ) * N.coeff k

/-! ## Elementary properties of the periodic coefficient -/

theorem periodicCoeff_sub_of_dvd {d k j : ℕ} (N : Polynomial ℂ) (hj : j ≤ k) (h : d ∣ j) :
    periodicCoeff N d (k - j) = periodicCoeff N d k := by
  obtain ⟨m, rfl⟩ := h
  unfold periodicCoeff
  congr 1
  conv_rhs => rw [show k = (k - d * m) + d * m by omega]
  exact (Nat.add_mul_mod_self_left _ _ _).symm

theorem periodicCoeff_eq_coeff {d k : ℕ} (N : Polynomial ℂ) (h : k < d) :
    periodicCoeff N d k = N.coeff k := by
  unfold periodicCoeff
  rw [Nat.mod_eq_of_lt h]

theorem periodicCoeff_shift {d k : ℕ} (N : Polynomial ℂ) :
    periodicCoeff N d (k + d) = periodicCoeff N d k := by
  unfold periodicCoeff
  rw [Nat.add_mod_right]

theorem coeff_eq_zero_of_le {d k : ℕ} {N : Polynomial ℂ} (hdeg : N.natDegree < d) (h : d ≤ k) :
    N.coeff k = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg h)

/-! ## The cyclotomic term -/

theorem sum_cycloTerm (d k : ℕ) : ∑ j ∈ Ioc 0 k, cycloTerm d j = ((d * (k / d) : ℕ) : ℂ) := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [show Ioc 0 (n + 1) = insert (n + 1) (Ioc 0 n) by
        ext x; simp only [mem_Ioc, mem_insert]; omega]
      rw [Finset.sum_insert (by simp), ih, Nat.succ_div]
      by_cases h : d ∣ (n + 1)
      · simp only [cycloTerm, h, if_pos, Nat.mul_add, Nat.mul_one, Nat.cast_add]
        ring
      · simp [cycloTerm, h]

theorem sum_cycloTerm_mul {d : ℕ} (N : Polynomial ℂ) (k : ℕ) :
    ∑ j ∈ Ioc 0 k, cycloTerm d j * periodicCoeff N d (k - j)
      = ((d * (k / d) : ℕ) : ℂ) * periodicCoeff N d k := by
  rw [← sum_cycloTerm d k, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp only [mem_Ioc] at hj
  by_cases h : d ∣ j
  · rw [periodicCoeff_sub_of_dvd N hj.2 h]
  · simp [cycloTerm, h]

/-! ## The two convolution sums -/

/-- The `π`-convolution against the periodic coefficient sequence. -/
def periodicConv (N : Polynomial ℂ) (d : ℕ) (π : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Ioc 0 k, π j * periodicCoeff N d (k - j)

/-- The `π`-convolution against the raw polynomial coefficients. -/
def polyConv (N : Polynomial ℂ) (π : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Ioc 0 k, π j * N.coeff (k - j)

theorem periodicConv_eq_polyConv_of_lt {d k : ℕ} (N : Polynomial ℂ) (π : ℕ → ℂ) (hk : k < d) :
    periodicConv N d π k = polyConv N π k := by
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp only [mem_Ioc] at hj
  rw [periodicCoeff_eq_coeff N (by omega)]

/-- Telescoping step: above the period, one period of the periodic convolution is exactly the
raw polynomial convolution. -/
theorem periodicConv_sub {d k : ℕ} {N : Polynomial ℂ} (hdeg : N.natDegree < d) (π : ℕ → ℂ)
    (hk : d ≤ k) :
    periodicConv N d π k - periodicConv N d π (k - d) = polyConv N π k := by
  have hsplit : (∑ j ∈ Ioc 0 (k - d), π j * periodicCoeff N d (k - j))
      + ∑ j ∈ Ioc (k - d) k, π j * periodicCoeff N d (k - j)
      = ∑ j ∈ Ioc 0 k, π j * periodicCoeff N d (k - j) :=
    Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (by omega)
  have h1 : (∑ j ∈ Ioc 0 (k - d), π j * periodicCoeff N d (k - j))
      = periodicConv N d π (k - d) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [mem_Ioc] at hj
    congr 1
    rw [show k - j = (k - d - j) + d by omega, periodicCoeff_shift]
  have h2 : (∑ j ∈ Ioc (k - d) k, π j * periodicCoeff N d (k - j))
      = ∑ j ∈ Ioc (k - d) k, π j * N.coeff (k - j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [mem_Ioc] at hj
    rw [periodicCoeff_eq_coeff N (by omega)]
  have hB : polyConv N π k = ∑ j ∈ Ioc (k - d) k, π j * N.coeff (k - j) := by
    rw [show polyConv N π k = ∑ j ∈ Ioc 0 k, π j * N.coeff (k - j) from rfl,
      ← Finset.sum_Ioc_consecutive (fun j => π j * N.coeff (k - j)) (Nat.zero_le (k - d))
        (by omega : k - d ≤ k)]
    have hzero : (∑ j ∈ Ioc 0 (k - d), π j * N.coeff (k - j)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      simp only [mem_Ioc] at hj
      rw [coeff_eq_zero_of_le hdeg (by omega), mul_zero]
    rw [hzero, zero_add]
  rw [hB, ← h2, show periodicConv N d π k = ∑ j ∈ Ioc 0 k, π j * periodicCoeff N d (k - j) from rfl,
    ← hsplit, h1]
  ring

/-! ## The main decomposition -/

/-- Pointwise reformulation: the local von Mangoldt equation at `k` is the statement that the
`π`-convolution equals `-(k % d)` times the periodic coefficient. -/
theorem localVonMangoldt_at_iff {d : ℕ} (N : Polynomial ℂ) (Λ : ℕ → ℂ) (k : ℕ) :
    (∑ j ∈ Ioc 0 k, Λ j * periodicCoeff N d (k - j) = (k : ℂ) * periodicCoeff N d k)
      ↔ periodicConv N d (fun j => cycloTerm d j - Λ j) k
          = -((k % d : ℕ) : ℂ) * periodicCoeff N d k := by
  have hconv : periodicConv N d (fun j => cycloTerm d j - Λ j) k
      = ((d * (k / d) : ℕ) : ℂ) * periodicCoeff N d k
        - ∑ j ∈ Ioc 0 k, Λ j * periodicCoeff N d (k - j) := by
    rw [show periodicConv N d (fun j => cycloTerm d j - Λ j) k
        = ∑ j ∈ Ioc 0 k, (cycloTerm d j - Λ j) * periodicCoeff N d (k - j) from rfl,
      ← sum_cycloTerm_mul N k, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have hcast : ((d * (k / d) : ℕ) : ℂ) + ((k % d : ℕ) : ℂ) = (k : ℂ) := by
    rw [← Nat.cast_add, Nat.div_add_mod]
  rw [hconv]
  constructor
  · intro h
    rw [h]
    linear_combination (periodicCoeff N d k) * hcast
  · intro h
    linear_combination -h + (periodicCoeff N d k) * hcast

/-- The characterising identity for the reciprocal-root power sums, transported to the periodic
convolution. -/
theorem periodicConv_spec_iff {d : ℕ} {N : Polynomial ℂ} (hd : 0 < d) (hdeg : N.natDegree < d)
    (π : ℕ → ℂ) :
    (∀ k, periodicConv N d π k = -((k % d : ℕ) : ℂ) * periodicCoeff N d k)
      ↔ IsRecipPowerSum N π := by
  constructor
  · intro h k hk
    rcases lt_or_ge k d with hlt | hge
    · have := h k
      rw [periodicConv_eq_polyConv_of_lt N π hlt] at this
      rw [show polyConv N π k = ∑ j ∈ Ioc 0 k, π j * N.coeff (k - j) from rfl] at this
      rw [this, Nat.mod_eq_of_lt hlt, periodicCoeff_eq_coeff N hlt]
    · have hstep := periodicConv_sub hdeg π hge
      rw [h k, h (k - d)] at hstep
      have hmod : (k - d) % d = k % d := by
        conv_rhs => rw [show k = (k - d) + d by omega]
        rw [Nat.add_mod_right]
      have hcoeff : periodicCoeff N d (k - d) = periodicCoeff N d k := by
        unfold periodicCoeff
        rw [hmod]
      rw [hmod, hcoeff] at hstep
      have hz : polyConv N π k = 0 := by rw [← hstep]; ring
      rw [show polyConv N π k = ∑ j ∈ Ioc 0 k, π j * N.coeff (k - j) from rfl] at hz
      rw [hz, coeff_eq_zero_of_le hdeg hge, mul_zero]
  · intro h k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [periodicConv]
      rcases lt_or_ge k d with hlt | hge
      · rw [periodicConv_eq_polyConv_of_lt N π hlt,
          show polyConv N π k = ∑ j ∈ Ioc 0 k, π j * N.coeff (k - j) from rfl, h k hk,
          Nat.mod_eq_of_lt hlt, periodicCoeff_eq_coeff N hlt]
      · have hstep := periodicConv_sub hdeg π hge
        have hrec := ih (k - d) (by omega)
        have hmod : (k - d) % d = k % d := by
          conv_rhs => rw [show k = (k - d) + d by omega]
          rw [Nat.add_mod_right]
        have hcoeff : periodicCoeff N d (k - d) = periodicCoeff N d k := by
          unfold periodicCoeff
          rw [hmod]
        rw [hmod, hcoeff] at hrec
        have hpc : polyConv N π k = 0 := by
          rw [show polyConv N π k = ∑ j ∈ Ioc 0 k, π j * N.coeff (k - j) from rfl, h k hk,
            coeff_eq_zero_of_le hdeg hge, mul_zero]
        rw [hpc] at hstep
        linear_combination hstep + hrec

/-- **Local von Mangoldt decomposition.**  For the `d`-periodic extension of the coefficients of a
polynomial `N` of degree `< d`, a sequence `Λ` is the local von Mangoldt sequence exactly when
`Λ k = d * [d ∣ k] - π k` with `π` the reciprocal-root power sum sequence of `N`.  The local data
therefore splits into a universal cyclotomic term fixed by the period and the power sums of the
reciprocal roots of the finite local polynomial. -/
theorem isLocalVonMangoldt_iff_isRecipPowerSum {d : ℕ} {N : Polynomial ℂ} (hd : 0 < d)
    (hdeg : N.natDegree < d) (Λ : ℕ → ℂ) :
    IsLocalVonMangoldt N d Λ ↔ IsRecipPowerSum N (fun k => cycloTerm d k - Λ k) := by
  rw [← periodicConv_spec_iff hd hdeg]
  constructor
  · intro h k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [periodicConv]
    · exact (localVonMangoldt_at_iff N Λ k).1 (h k hk)
  · intro h k hk
    exact (localVonMangoldt_at_iff N Λ k).2 (h k)

/-! ## Euler factors are exactly the geometric local sequences -/

/-- A local coefficient sequence is geometric — an Euler factor `1 / (1 - c X)` — exactly when its
local von Mangoldt sequence is the geometric sequence `k ↦ c ^ k`. -/
theorem geometric_vonMangoldt_iff {a : ℕ → ℂ} (ha : a 0 = 1) (c : ℂ) :
    (∀ k, 0 < k → ∑ j ∈ Ioc 0 k, c ^ j * a (k - j) = (k : ℂ) * a k) ↔ (∀ k, a k = c ^ k) := by
  constructor
  · intro h k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa using ha
      have hterm : ∀ j ∈ Ioc 0 k, c ^ j * a (k - j) = c ^ k := by
        intro j hj
        simp only [mem_Ioc] at hj
        rw [ih (k - j) (by omega), ← pow_add]
        congr 1
        omega
      have hsum : ∑ j ∈ Ioc 0 k, c ^ j * a (k - j) = (k : ℂ) * c ^ k := by
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ioc, Nat.sub_zero,
          nsmul_eq_mul]
      have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hres := h k hk
      rw [hsum] at hres
      exact (mul_right_injective₀ hk' hres).symm
  · intro h k hk
    have hterm : ∀ j ∈ Ioc 0 k, c ^ j * a (k - j) = c ^ k := by
      intro j hj
      simp only [mem_Ioc] at hj
      rw [h (k - j), ← pow_add]
      congr 1
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul,
      h k]

/-- The periodic extension of `N` is geometric exactly when `N` is the cyclotomic quotient
`(1 - X ^ d) / (1 - c X)`, i.e. when the reciprocal roots of `N` are the `d`-th roots of unity
other than `c`. -/
theorem periodicCoeff_geometric_iff {d : ℕ} {N : Polynomial ℂ} (hd : 0 < d) (c : ℂ) :
    (∀ k, periodicCoeff N d k = c ^ k) ↔ (c ^ d = 1 ∧ ∀ i, i < d → N.coeff i = c ^ i) := by
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · have h0 := h 0
      have hdd := h d
      rw [periodicCoeff, Nat.mod_self] at hdd
      rw [periodicCoeff, Nat.zero_mod] at h0
      rw [← hdd, h0, pow_zero]
    · have := h i
      rwa [periodicCoeff_eq_coeff N hi] at this
  · rintro ⟨hc, hN⟩ k
    rw [periodicCoeff, hN (k % d) (Nat.mod_lt _ hd)]
    conv_rhs => rw [show k = d * (k / d) + k % d from (Nat.div_add_mod k d).symm]
    rw [pow_add, pow_mul, hc, one_pow, one_mul]

/-- **Euler factor criterion.**  The local coefficient of period `d` attached to `N` is the Euler
factor `1 / (1 - c X)` — equivalently its local von Mangoldt sequence is `k ↦ c ^ k` — exactly when
`c ^ d = 1` and `N` is the cyclotomic quotient `(1 - X ^ d) / (1 - c X)`.  Combined with the
decomposition theorem, this says the reciprocal roots of `N` are the `d`-th roots of unity other
than `c`. -/
theorem isLocalVonMangoldt_geometric_iff {d : ℕ} {N : Polynomial ℂ} (hd : 0 < d)
    (h0 : N.coeff 0 = 1) (c : ℂ) :
    IsLocalVonMangoldt N d (fun k => c ^ k) ↔ (c ^ d = 1 ∧ ∀ i, i < d → N.coeff i = c ^ i) := by
  have ha : periodicCoeff N d 0 = 1 := by
    unfold periodicCoeff
    rw [Nat.zero_mod, h0]
  rw [show IsLocalVonMangoldt N d (fun k => c ^ k)
      ↔ ∀ k, 0 < k → ∑ j ∈ Ioc 0 k, c ^ j * periodicCoeff N d (k - j)
        = (k : ℂ) * periodicCoeff N d k from Iff.rfl,
    geometric_vonMangoldt_iff ha c, periodicCoeff_geometric_iff hd c]

/-- The local von Mangoldt sequence of a normalised local coefficient is unique. -/
theorem isLocalVonMangoldt_unique {d : ℕ} {N : Polynomial ℂ} (h0 : N.coeff 0 = 1)
    {Λ Λ' : ℕ → ℂ} (h : IsLocalVonMangoldt N d Λ) (h' : IsLocalVonMangoldt N d Λ') :
    ∀ k, 0 < k → Λ k = Λ' k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hsum : ∑ j ∈ Ioc 0 k, (Λ j - Λ' j) * periodicCoeff N d (k - j) = 0 := by
      have hsplit : ∑ j ∈ Ioc 0 k, (Λ j - Λ' j) * periodicCoeff N d (k - j)
          = (∑ j ∈ Ioc 0 k, Λ j * periodicCoeff N d (k - j))
            - ∑ j ∈ Ioc 0 k, Λ' j * periodicCoeff N d (k - j) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsplit, h k hk, h' k hk, sub_self]
    have hterm : ∀ j ∈ Ioc 0 k, j ≠ k → (Λ j - Λ' j) * periodicCoeff N d (k - j) = 0 := by
      intro j hj hjk
      simp only [mem_Ioc] at hj
      rw [ih j (by omega) hj.1, sub_self, zero_mul]
    have hmem : k ∈ Ioc 0 k := by simp [hk]
    rw [Finset.sum_eq_single_of_mem k hmem hterm, Nat.sub_self] at hsum
    have ha : periodicCoeff N d 0 = 1 := by
      unfold periodicCoeff
      rw [Nat.zero_mod, h0]
    rw [ha, mul_one, sub_eq_zero] at hsum
    exact hsum

/-! ## The reciprocal-root power sums are genuine power sums -/

/-- The polynomial `∏ (1 - y * X)` attached to a multiset `y` of reciprocal roots. -/
def recipFactor (y : Multiset ℂ) : Polynomial ℂ :=
  (y.map fun t => 1 - Polynomial.C t * Polynomial.X).prod

theorem recipFactor_zero : recipFactor 0 = 1 := by simp [recipFactor]

theorem recipFactor_cons (t : ℂ) (y : Multiset ℂ) :
    recipFactor (t ::ₘ y) = (1 - Polynomial.C t * Polynomial.X) * recipFactor y := by
  simp [recipFactor]

theorem coeff_linear_mul (t : ℂ) (P : Polynomial ℂ) (i : ℕ) :
    ((1 - Polynomial.C t * Polynomial.X) * P).coeff i
      = P.coeff i - t * (if i = 0 then 0 else P.coeff (i - 1)) := by
  rcases i with _ | m
  · simp [sub_mul, Polynomial.mul_coeff_zero]
  · simp [sub_mul, Polynomial.coeff_C_mul, mul_assoc, Polynomial.coeff_X_mul]

theorem sum_Ioc_zero_eq_range (k : ℕ) (f : ℕ → ℂ) :
    ∑ j ∈ Ioc 0 k, f j = ∑ i ∈ Finset.range k, f (i + 1) := by
  rw [show Ioc 0 k = Ico 1 (k + 1) by ext x; simp only [mem_Ioc, mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

/-- The sequence attached to `N = ∏ (1 - y * X)` by `IsRecipPowerSum` is the sequence of power sums
of the reciprocal roots `y`. -/
theorem isRecipPowerSum_recipFactor (y : Multiset ℂ) :
    IsRecipPowerSum (recipFactor y) fun k => (y.map fun t => t ^ k).sum := by
  induction y using Multiset.induction_on with
  | empty =>
      intro k hk
      simp [recipFactor_zero, Polynomial.coeff_one, Nat.ne_of_gt hk]
  | cons t y ih =>
      intro k hk
      set P : Polynomial ℂ := recipFactor y with hPdef
      set Q : ℕ → ℂ := fun i => if i = 0 then 0 else P.coeff (i - 1) with hQdef
      set π : ℕ → ℂ := fun m => (y.map fun u => u ^ m).sum with hπdef
      have hcoeff : ∀ i, (recipFactor (t ::ₘ y)).coeff i = P.coeff i - t * Q i := by
        intro i
        rw [recipFactor_cons, coeff_linear_mul]
      have hpi : ∀ m, ((t ::ₘ y).map fun u => u ^ m).sum = t ^ m + π m := by
        intro m
        simp [hπdef]
      -- the four pieces
      have hT2 : ∑ j ∈ Ioc 0 k, π j * Q (k - j) = -((k - 1 : ℕ) : ℂ) * P.coeff (k - 1) := by
        have hshrink : ∑ j ∈ Ioc 0 k, π j * Q (k - j)
            = ∑ j ∈ Ioc 0 (k - 1), π j * P.coeff (k - 1 - j) := by
          rw [show Ioc 0 k = insert k (Ioc 0 (k - 1)) by
            ext x; simp only [mem_Ioc, mem_insert]; omega,
            Finset.sum_insert (by simp)]
          have hzero : π k * Q (k - k) = 0 := by simp [hQdef]
          rw [hzero, zero_add]
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [mem_Ioc] at hj
          have : k - j ≠ 0 := by omega
          rw [show Q (k - j) = P.coeff (k - j - 1) by simp [hQdef, this]]
          congr 2
          omega
        rw [hshrink]
        rcases Nat.eq_zero_or_pos (k - 1) with hk1 | hk1
        · rw [hk1]
          simp
        · exact ih (k - 1) hk1
      have hT34 : (∑ j ∈ Ioc 0 k, t ^ j * P.coeff (k - j))
          - t * ∑ j ∈ Ioc 0 k, t ^ j * Q (k - j) = t * P.coeff (k - 1) := by
        have hshrink : ∑ j ∈ Ioc 0 k, t ^ j * Q (k - j)
            = ∑ j ∈ Ioc 0 (k - 1), t ^ j * P.coeff (k - 1 - j) := by
          rw [show Ioc 0 k = insert k (Ioc 0 (k - 1)) by
            ext x; simp only [mem_Ioc, mem_insert]; omega,
            Finset.sum_insert (by simp)]
          have hzero : t ^ k * Q (k - k) = 0 := by simp [hQdef]
          rw [hzero, zero_add]
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [mem_Ioc] at hj
          have : k - j ≠ 0 := by omega
          rw [show Q (k - j) = P.coeff (k - j - 1) by simp [hQdef, this]]
          congr 2
          omega
        rw [hshrink, sum_Ioc_zero_eq_range, sum_Ioc_zero_eq_range, Finset.mul_sum]
        have hg : ∀ i, t * (t ^ (i + 1) * P.coeff (k - 1 - (i + 1)))
            = t ^ (i + 1 + 1) * P.coeff (k - (i + 1 + 1)) := by
          intro i
          rw [← mul_assoc, ← pow_succ']
          congr 2
          omega
        rw [Finset.sum_congr rfl fun i _ => hg i]
        rw [show k = (k - 1) + 1 by omega]
        rw [Finset.sum_range_succ' (fun i => t ^ (i + 1) * P.coeff (k - 1 + 1 - (i + 1)))]
        simp
      have hQk : Q k = P.coeff (k - 1) := by simp [hQdef, Nat.ne_of_gt hk]
      have hcast : ((k - 1 : ℕ) : ℂ) + 1 = (k : ℂ) := by
        have hstep : ((k - 1 : ℕ) : ℂ) + 1 = ((k - 1 + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [hstep, show k - 1 + 1 = k by omega]
      have hexpand : ∑ j ∈ Ioc 0 k, ((t ::ₘ y).map fun u => u ^ j).sum
            * (recipFactor (t ::ₘ y)).coeff (k - j)
          = (∑ j ∈ Ioc 0 k, π j * P.coeff (k - j))
            - t * (∑ j ∈ Ioc 0 k, π j * Q (k - j))
            + ((∑ j ∈ Ioc 0 k, t ^ j * P.coeff (k - j))
              - t * ∑ j ∈ Ioc 0 k, t ^ j * Q (k - j)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hpi j, hcoeff (k - j)]
        ring
      rw [hexpand, ih k hk, hT2, hT34, hcoeff k, hQk]
      rw [← hcast]
      ring

/-! ## Torsion of the reciprocal roots forces a finite local von Mangoldt range -/

theorem cycloTerm_periodic (d : ℕ) : Function.Periodic (cycloTerm d) d := by
  intro k
  have hiff : d ∣ (k + d) ↔ d ∣ k := Nat.dvd_add_self_right
  simp only [cycloTerm, hiff]

/-- If the reciprocal-root power sums are periodic — the case in which every reciprocal root of `N`
is a root of unity — then the local von Mangoldt sequence is periodic, hence takes finitely many
values. -/
theorem periodic_of_periodic_recipPowerSum {d M : ℕ} {Λ π : ℕ → ℂ}
    (hΛ : ∀ k, π k = cycloTerm d k - Λ k) (hπ : Function.Periodic π M) :
    Function.Periodic Λ (d * M) := by
  have hcyc : Function.Periodic (cycloTerm d) (d * M) := by
    rw [Nat.mul_comm]
    exact (cycloTerm_periodic d).nat_mul M
  have hπ' : Function.Periodic π (d * M) := hπ.nat_mul d
  intro k
  have h1 := hcyc k
  have h2 := hπ' k
  have e1 := hΛ (k + d * M)
  have e2 := hΛ k
  linear_combination e1 - e2 - h2 + h1

theorem finite_range_of_periodic {f : ℕ → ℂ} {n : ℕ} (hn : 0 < n) (hf : Function.Periodic f n) :
    (Set.range f).Finite := by
  have hmod : ∀ k, f k = f (k % n) := by
    intro k
    conv_lhs => rw [← Nat.mod_add_div' k n]
    exact (hf.nat_mul (k / n)) (k % n)
  have hsub : Set.range f ⊆ f '' (Set.Iio n) := by
    rintro x ⟨k, rfl⟩
    exact ⟨k % n, Nat.mod_lt _ hn, (hmod k).symm⟩
  exact Set.Finite.subset ((Set.finite_Iio n).image f) hsub

end

end RHTower
