import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheOddWeilLedgerIsFrustratedOnlyByPrimes

/-!
# The frustration index controls the ground energy

A signed incidence form `c` on a finite set carries a ℤ/2 **orientation class**: its switching
class `{s_i s_j c_ij : s_i = ±1}`.  The class is trivial exactly when the form is balanced.  This
module attaches to the class an integer, the **frustration index**
`ν(c) = min_s #{(i, j) : i ≠ j, s_i s_j c_ij > 0}` (ordered pairs, so every unordered misaligned
overlap is counted twice), and a mass, the **frustration mass**
`ν_w(c) = min_s Σ_{s_i s_j c_ij > 0} |c_ij|`, and relates both to the **signed Dirichlet form**

    D_c(x) = Σ_{i ≠ j} |c_ij| (x_i + sgn(c_ij) x_j)²,

whose ground energy is the orientation-sensitive part of the incidence energy
(`signedDirichletForm_eq`: `D_c(x) = 2 Σ_i deg_i x_i² + 2 Σ_{i≠j} c_ij x_i x_j`).

* **Switching covariance** (`signedDirichletForm_switch`, `frustrationIndex_switch`): the form and
  the index depend only on the orientation class.
* **Balance** (`isBalanced_iff_frustrationIndex_eq_zero`): `ν(c) = 0 ⟺ c` is balanced.
* **The sign vectors read the mass** (`signedDirichletForm_signVector`): at a sign vector `s`,
  `D_c(s) = 4 · (misaligned mass of s)`, hence the ground energy on the unit sphere is at most
  `4 ν_w(c) / n` (`groundEnergy_le_frustrationMass`).
* **Ground energy zero is balance** (`isBalanced_of_signedDirichletForm_eq_zero`,
  `exists_signVector_signedDirichletForm_eq_zero_of_isBalanced`): a nowhere-vanishing profile of
  zero Dirichlet energy switches the form into alignment, and a balanced form has a sign vector
  of zero energy.  On a connected pattern every nonzero zero-energy profile is nowhere vanishing
  (`ne_zero_of_signedDirichletForm_eq_zero`), so the ground energy of a connected form vanishes
  iff the form is balanced (`groundEnergy_eq_zero_iff_isBalanced`).

The arithmetic instance is the odd Weil ledger: its only positive couplings sit on prime-sum
edges, so its frustration index is at most the number of ordered prime-sum pairs
(`frustrationIndex_oddWeilLedger_le`).
-/

open Finset

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The signed Dirichlet form -/

/-- The orientation sign of a coupling: `+1` for a positive (frustrating) overlap, `−1` otherwise.
At a vanishing coupling the value is irrelevant, since it is always multiplied by `|c_ij| = 0`. -/
def orientSign (t : ℝ) : ℝ := if 0 < t then 1 else -1

theorem orientSign_sq (t : ℝ) : orientSign t ^ 2 = 1 := by
  unfold orientSign; split_ifs <;> norm_num

theorem orientSign_of_pos {t : ℝ} (h : 0 < t) : orientSign t = 1 := if_pos h

theorem orientSign_of_neg {t : ℝ} (h : t < 0) : orientSign t = -1 := if_neg (not_lt.2 h.le)

/-- `|t| (x + sgn(t) y)² = |t| x² + |t| y² + 2 t x y`: the edge term of the Dirichlet form. -/
theorem abs_mul_sq_orientSign (t x y : ℝ) :
    |t| * (x + orientSign t * y) ^ 2 = |t| * x ^ 2 + |t| * y ^ 2 + 2 * t * x * y := by
  rcases lt_trichotomy 0 t with h | h | h
  · rw [orientSign_of_pos h, abs_of_pos h]; ring
  · subst h; simp
  · rw [orientSign_of_neg h, abs_of_neg h]; ring

/-- At a sign pair `a, b = ±1` the edge term is `4|t|` on a misaligned overlap and `0` otherwise. -/
theorem edge_signVector {a b t : ℝ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    |t| * (a + orientSign t * b) ^ 2 = 4 * (if 0 < a * b * t then |t| else 0) := by
  rcases lt_trichotomy 0 t with ht | rfl | ht
  · rw [orientSign_of_pos ht, abs_of_pos ht, one_mul]
    rcases sq_eq_one_iff.1 ha with rfl | rfl <;> rcases sq_eq_one_iff.1 hb with rfl | rfl
    · rw [if_pos (by linarith)]; ring
    · rw [if_neg (by norm_num; linarith)]; ring
    · rw [if_neg (by norm_num; linarith)]; ring
    · rw [if_pos (by norm_num; linarith)]; ring
  · simp
  · rw [orientSign_of_neg ht, abs_of_neg ht]
    rcases sq_eq_one_iff.1 ha with rfl | rfl <;> rcases sq_eq_one_iff.1 hb with rfl | rfl
    · rw [if_neg (by norm_num; linarith)]; ring
    · rw [if_pos (by norm_num; linarith)]; ring
    · rw [if_pos (by norm_num; linarith)]; ring
    · rw [if_neg (by norm_num; linarith)]; ring

/-- The signed Dirichlet form `D_c(x) = Σ_{i ≠ j} |c_ij| (x_i + sgn(c_ij) x_j)²`. -/
def signedDirichletForm (c : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else |c i j| * (x i + orientSign (c i j) * x j) ^ 2

/-- The degree of a point: the total absolute coupling it meets. -/
def pointDegree (c : ι → ι → ℝ) (i : ι) : ℝ := ∑ j, if i = j then 0 else |c i j|

omit [Fintype ι] in
theorem edgeTerm_nonneg (c : ι → ι → ℝ) (x : ι → ℝ) (i j : ι) :
    0 ≤ (if i = j then (0 : ℝ) else |c i j| * (x i + orientSign (c i j) * x j) ^ 2) := by
  split_ifs
  · exact le_rfl
  · positivity

theorem signedDirichletForm_nonneg (c : ι → ι → ℝ) (x : ι → ℝ) :
    0 ≤ signedDirichletForm c x :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => edgeTerm_nonneg c x i j

/-- **The Dirichlet form is the orientation-sensitive incidence energy**:
`D_c(x) = 2 Σ_i deg_i x_i² + 2 Σ_{i≠j} c_ij x_i x_j` for symmetric `c`. -/
theorem signedDirichletForm_eq {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) (x : ι → ℝ) :
    signedDirichletForm c x =
      2 * ∑ i, pointDegree c i * x i ^ 2 +
        2 * ∑ i, ∑ j, if i = j then 0 else c i j * x i * x j := by
  have h1 : ∀ i j : ι, (if i = j then (0 : ℝ) else |c i j| * (x i + orientSign (c i j) * x j) ^ 2)
      = (if i = j then 0 else |c i j| * x i ^ 2) + (if i = j then 0 else |c i j| * x j ^ 2)
        + 2 * (if i = j then 0 else c i j * x i * x j) := by
    intro i j
    split_ifs
    · simp
    · rw [abs_mul_sq_orientSign]; ring
  have hA : ∑ i, ∑ j, (if i = j then (0 : ℝ) else |c i j| * x i ^ 2)
      = ∑ i, pointDegree c i * x i ^ 2 := by
    refine sum_congr rfl fun i _ => ?_
    unfold pointDegree
    rw [sum_mul]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hB : ∑ i, ∑ j, (if i = j then (0 : ℝ) else |c i j| * x j ^ 2)
      = ∑ i, pointDegree c i * x i ^ 2 := by
    rw [← hA, sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), hc j i]
  have hC : ∑ i, ∑ j, 2 * (if i = j then (0 : ℝ) else c i j * x i * x j)
      = 2 * ∑ i, ∑ j, (if i = j then 0 else c i j * x i * x j) := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
  unfold signedDirichletForm
  simp_rw [h1]
  simp only [sum_add_distrib]
  rw [hA, hB, hC]
  ring

/-! ### Switching covariance -/

/-- The orientation sign is multiplicative against a sign pair away from `0`. -/
theorem orientSign_mul_sign {s t u : ℝ} (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (hu : u ≠ 0) :
    orientSign (s * t * u) = s * t * orientSign u := by
  have hst : s * t = 1 ∨ s * t = -1 := by
    rcases sq_eq_one_iff.1 hs with rfl | rfl <;> rcases sq_eq_one_iff.1 ht with rfl | rfl <;>
      norm_num
  rcases hst with h | h
  · rw [h, one_mul, one_mul]
  · rw [h, neg_one_mul, neg_one_mul]
    unfold orientSign
    rcases lt_or_gt_of_ne hu with hu' | hu'
    · rw [if_pos (by linarith), if_neg (not_lt.2 hu'.le)]; norm_num
    · rw [if_neg (not_lt.2 (by linarith)), if_pos hu']

/-- **Switching covariance**: `D_{s·c}(s x) = D_c(x)` for every sign vector `s`. -/
theorem signedDirichletForm_switch {s : ι → ℝ} (hs : ∀ i, s i ^ 2 = 1) (c : ι → ι → ℝ)
    (x : ι → ℝ) :
    signedDirichletForm (switchCoupling s c) (fun i => s i * x i) = signedDirichletForm c x := by
  unfold signedDirichletForm
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · simp [hij]
  rw [if_neg hij, if_neg hij]
  by_cases hc : c i j = 0
  · simp [switchCoupling, hc]
  simp only [switchCoupling]
  rw [orientSign_mul_sign (hs i) (hs j) hc]
  have hsi : |s i| = 1 := abs_eq_one_of_sq (hs i)
  have hsj : |s j| = 1 := abs_eq_one_of_sq (hs j)
  rw [abs_mul, abs_mul, hsi, hsj, one_mul, one_mul]
  have : s i * x i + s i * s j * orientSign (c i j) * (s j * x j)
      = s i * (x i + orientSign (c i j) * x j) := by
    have h2 : s j * s j = 1 := by rw [← sq]; exact hs j
    linear_combination (s i * orientSign (c i j) * x j) * h2
  rw [this, mul_pow, hs i, one_mul]

/-! ### The frustration index and mass -/

/-- The misaligned mass of a sign vector: the absolute coupling of the overlaps it leaves
positive (ordered pairs). -/
def misalignedMass (s : ι → ℝ) (c : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, if i ≠ j ∧ 0 < s i * s j * c i j then |c i j| else 0

/-- The misaligned count of a sign vector (ordered pairs). -/
def misalignedCount (s : ι → ℝ) (c : ι → ι → ℝ) : ℕ :=
  (univ.filter fun p : ι × ι => p.1 ≠ p.2 ∧ 0 < s p.1 * s p.2 * c p.1 p.2).card

/-- A sign vector: a `±1`-valued profile. -/
def IsSignVector (s : ι → ℝ) : Prop := ∀ i, s i ^ 2 = 1

omit [Fintype ι] [DecidableEq ι] in
theorem isSignVector_one : IsSignVector (fun _ : ι => (1 : ℝ)) := fun _ => by norm_num

omit [Fintype ι] [DecidableEq ι] in
theorem IsSignVector.mul {s t : ι → ℝ} (hs : IsSignVector s) (ht : IsSignVector t) :
    IsSignVector (fun i => s i * t i) := fun i => by rw [mul_pow, hs i, ht i, one_mul]

omit [Fintype ι] [DecidableEq ι] in
instance instNonemptySignVector : Nonempty {s : ι → ℝ // IsSignVector s} :=
  ⟨⟨fun _ => 1, isSignVector_one⟩⟩

/-- The **frustration index**: the least misaligned count over all switchings. -/
def frustrationIndex (c : ι → ι → ℝ) : ℕ :=
  sInf {k : ℕ | ∃ s : ι → ℝ, IsSignVector s ∧ misalignedCount s c = k}

/-- The **frustration mass**: the least misaligned mass over all switchings. -/
def frustrationMass (c : ι → ι → ℝ) : ℝ :=
  ⨅ s : {s : ι → ℝ // IsSignVector s}, misalignedMass s.1 c

theorem misalignedMass_nonneg (s : ι → ℝ) (c : ι → ι → ℝ) : 0 ≤ misalignedMass s c :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => by split_ifs <;> positivity

theorem frustrationIndex_mem (c : ι → ι → ℝ) :
    ∃ s : ι → ℝ, IsSignVector s ∧ misalignedCount s c = frustrationIndex c := by
  have h : ({k : ℕ | ∃ s : ι → ℝ, IsSignVector s ∧ misalignedCount s c = k}).Nonempty :=
    ⟨misalignedCount (fun _ => (1 : ℝ)) c, fun _ => (1 : ℝ), isSignVector_one, rfl⟩
  exact Nat.sInf_mem h

theorem frustrationIndex_le {s : ι → ℝ} (hs : IsSignVector s) (c : ι → ι → ℝ) :
    frustrationIndex c ≤ misalignedCount s c :=
  Nat.sInf_le ⟨s, hs, rfl⟩

theorem frustrationMass_le {s : ι → ℝ} (hs : IsSignVector s) (c : ι → ι → ℝ) :
    frustrationMass c ≤ misalignedMass s c :=
  ciInf_le ⟨0, by rintro _ ⟨t, rfl⟩; exact misalignedMass_nonneg _ _⟩
    (⟨s, hs⟩ : {s // IsSignVector s})

theorem frustrationMass_nonneg (c : ι → ι → ℝ) : 0 ≤ frustrationMass c :=
  le_ciInf fun s => misalignedMass_nonneg s.1 c

/-- Misalignment composes with switching: the misaligned pairs of `t` for `s·c` are those of
`s·t` for `c`. -/
theorem misalignedCount_switch (s t : ι → ℝ) (c : ι → ι → ℝ) :
    misalignedCount t (switchCoupling s c) = misalignedCount (fun i => s i * t i) c := by
  unfold misalignedCount
  congr 1
  ext p
  simp only [mem_filter, mem_univ, true_and, switchCoupling]
  have : s p.1 * t p.1 * (s p.2 * t p.2) * c p.1 p.2 =
      t p.1 * t p.2 * (s p.1 * s p.2 * c p.1 p.2) := by ring
  rw [this]

/-- **The frustration index is an orientation-class invariant.** -/
theorem frustrationIndex_switch {s : ι → ℝ} (hs : IsSignVector s) (c : ι → ι → ℝ) :
    frustrationIndex (switchCoupling s c) = frustrationIndex c := by
  apply le_antisymm
  · obtain ⟨t, ht, hteq⟩ := frustrationIndex_mem c
    rw [← hteq]
    have h := frustrationIndex_le (c := switchCoupling s c) (hs.mul ht)
    rw [misalignedCount_switch] at h
    refine le_trans h (le_of_eq ?_)
    congr 1
    funext i
    have h2 : s i * s i = 1 := by rw [← sq]; exact hs i
    calc s i * (s i * t i) = (s i * s i) * t i := by ring
      _ = t i := by rw [h2, one_mul]
  · obtain ⟨t, ht, hteq⟩ := frustrationIndex_mem (switchCoupling s c)
    rw [← hteq, misalignedCount_switch]
    exact frustrationIndex_le (hs.mul ht) c

/-! ### Balance is frustration index zero -/

theorem misalignedCount_eq_zero_iff (s : ι → ℝ) (c : ι → ι → ℝ) :
    misalignedCount s c = 0 ↔ HasNonpositiveOverlaps (switchCoupling s c) := by
  unfold misalignedCount HasNonpositiveOverlaps
  rw [card_eq_zero, filter_eq_empty_iff]
  constructor
  · intro h i j hij
    have := h (mem_univ (i, j))
    simp only [ne_eq, not_and, not_lt] at this
    exact this hij
  · intro h p _
    simp only [ne_eq, not_and, not_lt]
    exact fun hp => h p.1 p.2 hp

/-- **Balance is frustration index zero.** -/
theorem isBalanced_iff_frustrationIndex_eq_zero (c : ι → ι → ℝ) :
    IsBalanced c ↔ frustrationIndex c = 0 := by
  constructor
  · rintro ⟨s, hs, hz⟩
    apply le_antisymm _ (Nat.zero_le _)
    have := frustrationIndex_le (c := c) hs
    rwa [(misalignedCount_eq_zero_iff s c).2 hz] at this
  · intro h
    obtain ⟨s, hs, hseq⟩ := frustrationIndex_mem c
    rw [h] at hseq
    exact ⟨s, hs, (misalignedCount_eq_zero_iff s c).1 hseq⟩

/-! ### Sign vectors read the mass -/

/-- At a sign vector the Dirichlet form is four times the misaligned mass. -/
theorem signedDirichletForm_signVector {s : ι → ℝ} (hs : IsSignVector s) (c : ι → ι → ℝ) :
    signedDirichletForm c s = 4 * misalignedMass s c := by
  unfold signedDirichletForm misalignedMass
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  by_cases hij : i = j
  · simp [hij]
  rw [if_neg hij]
  simp only [ne_eq, hij, not_false_eq_true, true_and]
  exact edge_signVector (hs i) (hs j)

/-- The ground energy of the Dirichlet form on the unit sphere. -/
def groundEnergy (c : ι → ι → ℝ) : ℝ :=
  ⨅ x : {x : ι → ℝ // ∑ i, x i ^ 2 = 1}, signedDirichletForm c x.1

instance instNonemptyUnitSphere [Nonempty ι] : Nonempty {x : ι → ℝ // ∑ i, x i ^ 2 = 1} :=
  ⟨⟨fun i => if i = Classical.arbitrary ι then 1 else 0, by
    simp only [ite_pow, one_pow, zero_pow two_ne_zero]
    simp [sum_ite_eq']⟩⟩

theorem groundEnergy_nonneg (c : ι → ι → ℝ) [Nonempty ι] : 0 ≤ groundEnergy c :=
  le_ciInf fun x => signedDirichletForm_nonneg c x.1

theorem groundEnergy_le (c : ι → ι → ℝ) {x : ι → ℝ} (hx : ∑ i, x i ^ 2 = 1) :
    groundEnergy c ≤ signedDirichletForm c x :=
  ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact signedDirichletForm_nonneg c y.1⟩
    (⟨x, hx⟩ : {x : ι → ℝ // ∑ i, x i ^ 2 = 1})

theorem signedDirichletForm_smul (c : ι → ι → ℝ) (r : ℝ) (x : ι → ℝ) :
    signedDirichletForm c (fun i => r * x i) = r ^ 2 * signedDirichletForm c x := by
  unfold signedDirichletForm
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **The ground energy is at most `4 ν_w(c) / n`**: the normalized sign vector attaining the
frustration mass is a trial profile. -/
theorem groundEnergy_le_frustrationMass (c : ι → ι → ℝ) [Nonempty ι] :
    groundEnergy c ≤ 4 * frustrationMass c / Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have key : ∀ s : {s : ι → ℝ // IsSignVector s},
      groundEnergy c * Fintype.card ι / 4 ≤ misalignedMass s.1 c := by
    rintro ⟨s, hs⟩
    have hnorm : ∑ i, (1 / Real.sqrt (Fintype.card ι) * s i) ^ 2 = 1 := by
      have h1 : ∀ i, (1 / Real.sqrt (Fintype.card ι) * s i) ^ 2 = 1 / Fintype.card ι := by
        intro i
        rw [mul_pow, hs i, mul_one, div_pow, one_pow, Real.sq_sqrt hn.le]
      simp only [h1, sum_const, card_univ, nsmul_eq_mul]
      field_simp
    have h := groundEnergy_le c hnorm
    rw [signedDirichletForm_smul, signedDirichletForm_signVector hs, div_pow, one_pow,
      Real.sq_sqrt hn.le, show 1 / (Fintype.card ι : ℝ) * (4 * misalignedMass s c)
        = 4 * misalignedMass s c / Fintype.card ι by ring, le_div_iff₀ hn] at h
    linarith
  have h2 : groundEnergy c * Fintype.card ι / 4 ≤ frustrationMass c := le_ciInf key
  rw [le_div_iff₀ hn]
  linarith

/-! ### Ground energy zero is balance -/

/-- A nowhere-vanishing profile of zero Dirichlet energy switches the form into alignment. -/
theorem isBalanced_of_signedDirichletForm_eq_zero {c : ι → ι → ℝ} {x : ι → ℝ}
    (hx : ∀ i, x i ≠ 0) (h : signedDirichletForm c x = 0) : IsBalanced c := by
  -- every edge term vanishes
  have hterm : ∀ i j, i ≠ j → |c i j| * (x i + orientSign (c i j) * x j) ^ 2 = 0 := by
    intro i j hij
    have h1 := (sum_eq_zero_iff_of_nonneg fun i' _ => sum_nonneg fun j' _ =>
      edgeTerm_nonneg c x i' j').1 h i (mem_univ i)
    have h2 := (sum_eq_zero_iff_of_nonneg fun j' _ => edgeTerm_nonneg c x i j').1 h1 j (mem_univ j)
    simpa [hij] using h2
  refine ⟨fun i => orientSign (x i), fun i => orientSign_sq _, fun i j hij => ?_⟩
  simp only [switchCoupling]
  rcases lt_trichotomy 0 (c i j) with hc | hc | hc
  · -- positive coupling: `x_i = -x_j`, so the signs of `x_i, x_j` are opposite
    have h0 := hterm i j hij
    rw [orientSign_of_pos hc, one_mul, abs_of_pos hc] at h0
    have hxx : x i + x j = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hc.ne'
      · exact (pow_eq_zero_iff two_ne_zero).1 h
    have hxj : x j = -x i := by linarith
    have hsign : orientSign (x j) = -orientSign (x i) := by
      rw [hxj]
      rcases lt_trichotomy 0 (x i) with h | h | h
      · rw [orientSign_of_pos h, orientSign_of_neg (by linarith)]
      · exact absurd h.symm (hx i)
      · rw [orientSign_of_neg h, orientSign_of_pos (by linarith)]; norm_num
    have hprod : orientSign (x i) * -orientSign (x i) * c i j = -(c i j) := by
      linear_combination (-(c i j)) * orientSign_sq (x i)
    rw [hsign, hprod]
    linarith
  · rw [← hc]; simp
  · -- negative coupling: `x_i = x_j`, so the signs agree
    have h0 := hterm i j hij
    rw [orientSign_of_neg hc, abs_of_neg hc] at h0
    have hxx : x i - x j = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h (by linarith)
      · have := (pow_eq_zero_iff two_ne_zero).1 h; linarith
    have hxj : x j = x i := by linarith
    have hprod : orientSign (x i) * orientSign (x i) * c i j = c i j := by
      linear_combination (c i j) * orientSign_sq (x i)
    rw [hxj, hprod]
    exact hc.le

/-- A balanced form has a sign vector of zero Dirichlet energy. -/
theorem exists_signVector_signedDirichletForm_eq_zero_of_isBalanced {c : ι → ι → ℝ}
    (hb : IsBalanced c) : ∃ s : ι → ℝ, IsSignVector s ∧ signedDirichletForm c s = 0 := by
  obtain ⟨s, hs, hz⟩ := hb
  refine ⟨s, hs, ?_⟩
  rw [signedDirichletForm_signVector hs]
  have : misalignedMass s c = 0 := by
    unfold misalignedMass
    refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => ?_
    rw [if_neg]
    rintro ⟨hij, hpos⟩
    have := hz i j hij
    simp only [switchCoupling] at this
    linarith
  rw [this]; ring

/-- Along an overlap `c_ij ≠ 0`, zero Dirichlet energy forces `|x_i| = |x_j|`. -/
theorem abs_eq_of_signedDirichletForm_eq_zero {c : ι → ι → ℝ} {x : ι → ℝ}
    (h : signedDirichletForm c x = 0) {i j : ι} (hij : i ≠ j) (hc : c i j ≠ 0) :
    |x i| = |x j| := by
  have h1 := (sum_eq_zero_iff_of_nonneg fun i' _ => sum_nonneg fun j' _ =>
    edgeTerm_nonneg c x i' j').1 h i (mem_univ i)
  have h2 := (sum_eq_zero_iff_of_nonneg fun j' _ => edgeTerm_nonneg c x i j').1 h1 j (mem_univ j)
  rw [if_neg hij] at h2
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (abs_eq_zero.1 h3) hc
  · have h4 := (pow_eq_zero_iff two_ne_zero).1 h3
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · rw [orientSign_of_neg hneg] at h4
      have : x i = x j := by linarith
      rw [this]
    · rw [orientSign_of_pos hpos] at h4
      have : x i = -x j := by linarith
      rw [this, abs_neg]

/-- Along a walk, zero Dirichlet energy propagates `|x|`. -/
theorem abs_eq_walkEnd_of_signedDirichletForm_eq_zero {c : ι → ι → ℝ} {x : ι → ℝ}
    (h : signedDirichletForm c x = 0) :
    ∀ (u : ι) (l : List ι), IsWalkFrom c u l → |x u| = |x (walkEnd u l)|
  | _, [], _ => rfl
  | u, y :: rest, ⟨huy, hc, hrest⟩ => by
    rw [walkEnd, abs_eq_of_signedDirichletForm_eq_zero h huy hc]
    exact abs_eq_walkEnd_of_signedDirichletForm_eq_zero h y rest hrest

/-- On a connected pattern a nonzero profile of zero Dirichlet energy vanishes nowhere. -/
theorem ne_zero_of_signedDirichletForm_eq_zero {c : ι → ι → ℝ}
    (hconn : ∀ u v : ι, IsJoined c u v) {x : ι → ℝ} (hx : x ≠ 0)
    (h : signedDirichletForm c x = 0) (i : ι) : x i ≠ 0 := by
  obtain ⟨u, hu⟩ : ∃ u, x u ≠ 0 := by
    by_contra hall
    exact hx (funext fun i => not_not.1 fun h => hall ⟨i, h⟩)
  obtain ⟨l, hl, hend⟩ := hconn u i
  have := abs_eq_walkEnd_of_signedDirichletForm_eq_zero h u l hl
  rw [hend] at this
  intro hi
  rw [hi, abs_zero, abs_eq_zero] at this
  exact hu this

/-- **The ground energy of a connected form vanishes iff the form is balanced.** -/
theorem groundEnergy_eq_zero_iff_isBalanced {c : ι → ι → ℝ} [Nonempty ι]
    (hconn : ∀ u v : ι, IsJoined c u v) :
    (∃ x : ι → ℝ, x ≠ 0 ∧ signedDirichletForm c x = 0) ↔ IsBalanced c := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact isBalanced_of_signedDirichletForm_eq_zero
      (ne_zero_of_signedDirichletForm_eq_zero hconn hx h) h
  · intro hb
    obtain ⟨s, hs, h⟩ := exists_signVector_signedDirichletForm_eq_zero_of_isBalanced hb
    refine ⟨s, fun h0 => ?_, h⟩
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have := hs i
    rw [h0] at this
    simp at this

/-! ### The odd Weil ledger -/

open scoped Classical in
/-- The prime-sum pairs of a sampled position set: ordered pairs `x ≠ y` whose positions sum to
the logarithm of a prime power. -/
def primeSumPairs (p : ι → ℝ) : Finset (ι × ι) :=
  univ.filter fun q : ι × ι => q.1 ≠ q.2 ∧
    ∃ n : ℕ, Real.exp (p q.1 + p q.2) = n ∧ 0 < ArithmeticFunction.vonMangoldt n

/-- **The frustration index of the odd Weil ledger is carried by prime sums**: the identity
switching leaves positive exactly the prime-sum overlaps, so `ν ≤ #primeSumPairs`. -/
theorem frustrationIndex_oddWeilLedger_le {p : ι → ℝ} (hp : ∀ x, 0 < p x)
    (hinj : Function.Injective p) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (b : ι → ℝ) :
    frustrationIndex (oddFold p (weilLedgerKernel α β) b) ≤ (primeSumPairs p).card := by
  refine le_trans (frustrationIndex_le isSignVector_one _) ?_
  unfold misalignedCount primeSumPairs
  apply card_le_card
  intro q hq
  simp only [mem_filter, mem_univ, true_and, one_mul] at hq ⊢
  exact ⟨hq.1, oddFold_pos_imp_primeSum hp hinj hα hβ hq.1 hq.2⟩

/-- **The frustration mass of the odd Weil ledger is carried by prime sums**: it is at most the
total positive coupling on the prime-sum pairs. -/
theorem frustrationMass_oddWeilLedger_le {p : ι → ℝ} (hp : ∀ x, 0 < p x)
    (hinj : Function.Injective p) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (b : ι → ℝ) :
    frustrationMass (oddFold p (weilLedgerKernel α β) b) ≤
      ∑ q ∈ primeSumPairs p, |oddFold p (weilLedgerKernel α β) b q.1 q.2| := by
  set c := oddFold p (weilLedgerKernel α β) b with hc
  refine le_trans (frustrationMass_le isSignVector_one c) ?_
  calc misalignedMass (fun _ => (1 : ℝ)) c
      ≤ ∑ i, ∑ j, (if (i, j) ∈ primeSumPairs p then |c i j| else 0) := by
        unfold misalignedMass
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        split_ifs with hP hmem hmem
        · exact le_rfl
        · exfalso
          apply hmem
          unfold primeSumPairs
          simp only [mem_filter, mem_univ, true_and]
          exact ⟨hP.1, oddFold_pos_imp_primeSum hp hinj hα hβ hP.1 (by simpa using hP.2)⟩
        · exact abs_nonneg _
        · exact le_rfl
    _ = ∑ q ∈ primeSumPairs p, |c q.1 q.2| := by
        rw [← Fintype.sum_prod_type', sum_ite_mem, univ_inter]

end

end GaloisForLFunctions.ArithmeticOrientationTheory
