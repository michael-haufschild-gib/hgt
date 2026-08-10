import GaloisForLFunctions.HTGeometry.AbelianZetaGas.GasAlgebra

/-!
# Uniqueness of the KMS functional on the gas algebra

Every normalised linear functional satisfying the exchange identity is the Gibbs functional.  The
argument is the card's: a monomial with nonzero net charge at some mode is pushed, one isometry at a
time, to a pure power that commutes with everything else and is therefore annihilated; a diagonal
monomial is peeled mode by mode, each block contributing its weight.
-/

namespace GaloisForLFunctions.HTGeometry

open GasWord

variable {M : Type*}

/-! ## Words inside the algebra -/

theorem single_mul_single_one (x y : GasWord M) :
    (MonoidAlgebra.single x (1 : ℂ)) * (MonoidAlgebra.single y 1)
      = MonoidAlgebra.single (x * y) 1 := by
  rw [MonoidAlgebra.single_mul_single, mul_one]

theorem gasV_pow (i : M) (n : ℕ) :
    (gasV i : GasAlgebra M) ^ n = MonoidAlgebra.single (gen i ^ n) 1 := by
  rw [gasV, MonoidAlgebra.single_pow, one_pow]

theorem gasW_pow (i : M) (n : ℕ) :
    (gasW i : GasAlgebra M) ^ n = MonoidAlgebra.single (cogen i ^ n) 1 := by
  rw [gasW, MonoidAlgebra.single_pow, one_pow]

theorem charge_cogen (i : M) : charge (cogen i) = Finsupp.single i (-1) := by
  refine Finsupp.ext fun j => ?_
  rw [charge_apply]
  by_cases hij : i = j
  · subst hij
    simp [cogen]
  · have h1 : (cogen i).raise j = 0 := by simp [cogen]
    have h2 : (cogen i).lower j = 0 := by
      show (Finsupp.single i 1 : M →₀ ℕ) j = 0
      exact Finsupp.single_eq_of_ne (Ne.symm hij)
    have h3 : (Finsupp.single i (-1 : ℤ)) j = 0 := Finsupp.single_eq_of_ne (Ne.symm hij)
    rw [h1, h2, h3]
    simp

theorem chi_cogen (q : M → ℂ) (i : M) : chi q (cogen i) = (q i)⁻¹ := by
  rw [chi, charge_cogen, zprod,
    Finsupp.prod_single_index (h := fun j k => q j ^ k) (zpow_zero (q i))]
  rw [zpow_neg, zpow_one]

theorem twist_gasW (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (i : M) :
    twist q hq (gasW i) = (q i)⁻¹ • gasW i := by
  rw [gasW, twist_single, chi_cogen q, one_mul, MonoidAlgebra.smul_single', mul_one]

/-! ## The two vanishing engines -/

variable (ψ : GasAlgebra M →ₗ[ℂ] ℂ)

/-- A pure isometry power commuting with the rest of the word kills the functional. -/
theorem gas_vanish_gen (q : M → ℂ) (hq : ∀ i, q i ≠ 0)
    (hexch : ∀ a b : GasAlgebra M, ψ (a * b) = ψ (b * twist q hq a))
    {i : M} {k : ℕ} (hk : q i ^ k ≠ 1) (z : GasWord M)
    (hcomm : gen i ^ k * z = z * gen i ^ k) :
    ψ (MonoidAlgebra.single (gen i ^ k * z) 1) = 0 := by
  have hcommA : (gasV i : GasAlgebra M) ^ k * MonoidAlgebra.single z 1
      = MonoidAlgebra.single z 1 * (gasV i : GasAlgebra M) ^ k := by
    rw [gasV_pow, single_mul_single_one, single_mul_single_one, hcomm]
  have h := kms_pow_eq_zero_of_commuting ψ (twist q hq) hexch (twist_gasV q hq i) hk hcommA
  rwa [gasV_pow, single_mul_single_one] at h

/-- A pure adjoint power commuting with the rest of the word kills the functional. -/
theorem gas_vanish_cogen (q : M → ℂ) (hq : ∀ i, q i ≠ 0)
    (hexch : ∀ a b : GasAlgebra M, ψ (a * b) = ψ (b * twist q hq a))
    {i : M} {k : ℕ} (hk : (q i)⁻¹ ^ k ≠ 1) (z : GasWord M)
    (hcomm : cogen i ^ k * z = z * cogen i ^ k) :
    ψ (MonoidAlgebra.single (cogen i ^ k * z) 1) = 0 := by
  have hcommA : (gasW i : GasAlgebra M) ^ k * MonoidAlgebra.single z 1
      = MonoidAlgebra.single z 1 * (gasW i : GasAlgebra M) ^ k := by
    rw [gasW_pow, single_mul_single_one, single_mul_single_one, hcomm]
  have h := kms_pow_eq_zero_of_commuting ψ (twist q hq) hexch (twist_gasW q hq i) hk hcommA
  rwa [gasW_pow, single_mul_single_one] at h

/-! ## Block calculus -/

theorem gen_pow_eq_block (i : M) (k : ℕ) : gen i ^ k = block i k 0 := by
  rw [gen_pow, block]
  refine GasWord.ext rfl ?_
  simp

theorem cogen_pow_eq_block (i : M) (k : ℕ) : cogen i ^ k = block i 0 k := by
  rw [cogen_pow, block]
  refine GasWord.ext ?_ rfl
  simp

theorem block_mul_block (i : M) (a b c d : ℕ) :
    block i a b * block i c d = block i (a + (c - b)) (d + (b - c)) := by
  refine GasWord.ext ?_ ?_ <;> refine Finsupp.ext fun j => ?_
  · rw [raise_apply_mul]
    by_cases hij : i = j
    · subst hij; simp [block]
    · simp [block, Finsupp.single_eq_of_ne (Ne.symm hij)]
  · rw [lower_apply_mul]
    by_cases hij : i = j
    · subst hij; simp [block]
    · simp [block, Finsupp.single_eq_of_ne (Ne.symm hij)]

theorem block_comm_disjoint {i : M} (a b : ℕ) {r : GasWord M}
    (h1 : r.raise i = 0) (h2 : r.lower i = 0) :
    block i a b * r = r * block i a b := by
  refine mul_comm_of_disjoint fun j => ?_
  by_cases hij : i = j
  · subst hij
    exact Or.inr ⟨h1, h2⟩
  · exact Or.inl ⟨by simp [block, Finsupp.single_eq_of_ne (Ne.symm hij)],
      by simp [block, Finsupp.single_eq_of_ne (Ne.symm hij)]⟩

/-! ## Weights of modulus less than one -/

theorem pow_ne_one_of_norm_lt {z : ℂ} (h : ‖z‖ < 1) {k : ℕ} (hk : 1 ≤ k) : z ^ k ≠ 1 := by
  intro hz
  have h1 : ‖z ^ k‖ = 1 := by rw [hz, norm_one]
  rw [norm_pow] at h1
  have hlt : ‖z‖ ^ k < 1 := pow_lt_one₀ (norm_nonneg z) h (by omega)
  linarith

theorem inv_pow_ne_one_of_norm_lt {z : ℂ} (h : ‖z‖ < 1) {k : ℕ} (hk : 1 ≤ k) :
    z⁻¹ ^ k ≠ 1 := by
  intro hz
  rw [inv_pow] at hz
  exact pow_ne_one_of_norm_lt h hk (inv_eq_one.mp hz)

/-! ## The exchange identity on single monomials -/

theorem gas_apply_single (y : GasWord M) (c : ℂ) :
    ψ (MonoidAlgebra.single y c) = c * ψ (MonoidAlgebra.single y 1) := by
  have hc : MonoidAlgebra.single y c = c • MonoidAlgebra.single y (1 : ℂ) := by
    rw [MonoidAlgebra.smul_single', mul_one]
  rw [hc, map_smul, smul_eq_mul]

theorem gas_exchange_word (q : M → ℂ) (hq : ∀ i, q i ≠ 0)
    (hexch : ∀ a b : GasAlgebra M, ψ (a * b) = ψ (b * twist q hq a)) (u v : GasWord M) :
    ψ (MonoidAlgebra.single (u * v) 1)
      = chi q u * ψ (MonoidAlgebra.single (v * u) 1) := by
  have h := hexch (MonoidAlgebra.single u 1) (MonoidAlgebra.single v 1)
  rw [single_mul_single_one, twist_single, one_mul, MonoidAlgebra.single_mul_single,
    one_mul] at h
  rw [h, gas_apply_single]

theorem zprod_ne_zero (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (f : M →₀ ℤ) : zprod q f ≠ 0 := by
  rw [zprod, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hq i)

theorem chi_ne_zero (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (x : GasWord M) : chi q x ≠ 0 :=
  zprod_ne_zero q hq _

/-! ## Off-diagonal vanishing -/

/-- **A mode with positive net charge kills the monomial.**  Each application of the exchange
identity contracts one isometry against the mode's adjoints, strictly shortening the lower
exponent while preserving the charge; at the end the mode contributes a pure isometry power, which
commutes with the rest of the word. -/
theorem gas_offdiag_pos (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (hqlt : ∀ i, ‖q i‖ < 1)
    (hexch : ∀ a b : GasAlgebra M, ψ (a * b) = ψ (b * twist q hq a))
    (i : M) {k : ℕ} (hk : 1 ≤ k) :
    ∀ (b : ℕ) (r : GasWord M), r.raise i = 0 → r.lower i = 0 →
      ψ (MonoidAlgebra.single (block i (b + k) b * r) 1) = 0 := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro r hr1 hr2
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · have hblock : block i (0 + k) 0 = gen i ^ k := by
        rw [gen_pow_eq_block, Nat.zero_add]
      rw [hblock]
      refine gas_vanish_gen ψ q hq hexch (pow_ne_one_of_norm_lt (hqlt i) hk) r ?_
      rw [gen_pow_eq_block]
      exact block_comm_disjoint k 0 hr1 hr2
    · have hb1 : k + (b - 0) = b + k := by omega
      have hb2 : b + (0 - b) = b := by omega
      have hfac : gen i ^ k * (block i b b * r) = block i (b + k) b * r := by
        rw [← mul_assoc, gen_pow_eq_block, block_mul_block, hb1, hb2]
      have hc1 : b + (k - b) = (b - k) + k := by omega
      have hc2 : (0 : ℕ) + (b - k) = b - k := by omega
      have hrev : (block i b b * r) * gen i ^ k = block i ((b - k) + k) (b - k) * r := by
        rw [gen_pow_eq_block, mul_assoc, ← block_comm_disjoint k 0 hr1 hr2, ← mul_assoc,
          block_mul_block, hc1, hc2]
      rw [← hfac, gas_exchange_word ψ q hq hexch, hrev,
        ih (b - k) (by omega) r hr1 hr2, mul_zero]

/-- **A mode with negative net charge kills the monomial.**  The mirror argument, contracting the
adjoints against the isometries. -/
theorem gas_offdiag_neg (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (hqlt : ∀ i, ‖q i‖ < 1)
    (hexch : ∀ a b : GasAlgebra M, ψ (a * b) = ψ (b * twist q hq a))
    (i : M) {k : ℕ} (hk : 1 ≤ k) :
    ∀ (a : ℕ) (r : GasWord M), r.raise i = 0 → r.lower i = 0 →
      ψ (MonoidAlgebra.single (block i a (a + k) * r) 1) = 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro r hr1 hr2
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have hblock : block i 0 (0 + k) = cogen i ^ k := by
        rw [cogen_pow_eq_block, Nat.zero_add]
      rw [hblock]
      refine gas_vanish_cogen ψ q hq hexch
        (inv_pow_ne_one_of_norm_lt (hqlt i) hk) r ?_
      rw [cogen_pow_eq_block]
      exact block_comm_disjoint 0 k hr1 hr2
    · have hb1 : (0 : ℕ) + (a - k) = a - k := by omega
      have hb2 : a + (k - a) = (a - k) + k := by omega
      have hsmall : cogen i ^ k * (block i a a * r) = block i (a - k) ((a - k) + k) * r := by
        rw [← mul_assoc, cogen_pow_eq_block, block_mul_block, hb1, hb2]
      have hc1 : a + (0 - a) = a := by omega
      have hc2 : k + (a - 0) = a + k := by omega
      have hbig : (block i a a * r) * cogen i ^ k = block i a (a + k) * r := by
        rw [cogen_pow_eq_block, mul_assoc, ← block_comm_disjoint 0 k hr1 hr2, ← mul_assoc,
          block_mul_block, hc1, hc2]
      have hstep := gas_exchange_word ψ q hq hexch (cogen i ^ k) (block i a a * r)
      rw [hsmall, hbig, ih (a - k) (by omega) r hr1 hr2] at hstep
      rcases mul_eq_zero.mp hstep.symm with h | h
      · exact absurd h (chi_ne_zero q hq _)
      · exact h

/-! ## Diagonal evaluation -/

theorem natToInt_eq_single_add_erase (f : M →₀ ℕ) (i : M) :
    natToInt f = Finsupp.single i (f i : ℤ) + natToInt (f.erase i) := by
  refine Finsupp.ext fun j => ?_
  rw [natToInt_apply, Finsupp.add_apply, natToInt_apply]
  by_cases hij : i = j
  · subst hij
    rw [Finsupp.single_eq_same, Finsupp.erase_same]
    simp
  · rw [Finsupp.single_eq_of_ne (Ne.symm hij), Finsupp.erase_ne (Ne.symm hij)]
    simp

theorem zprod_single_nat (q : M → ℂ) (i : M) (a : ℕ) :
    zprod q (Finsupp.single i (a : ℤ)) = q i ^ a := by
  rw [zprod, Finsupp.prod_single_index (h := fun j k => q j ^ k) (zpow_zero (q i)),
    zpow_natCast]

theorem zprod_natToInt_erase (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (f : M →₀ ℕ) (i : M) :
    zprod q (natToInt f) = q i ^ f i * zprod q (natToInt (f.erase i)) := by
  rw [natToInt_eq_single_add_erase f i, zprod_add q hq, zprod_single_nat]

/-- **The value of a diagonal monomial.**  Peeling one mode at a time, each block contributes its
weight, so a diagonal monomial has the Gibbs value `∏_i q_i^{n_i}`. -/
theorem gas_diag_value (q : M → ℂ) (hq : ∀ i, q i ≠ 0)
    (hexch : ∀ a b : GasAlgebra M, ψ (a * b) = ψ (b * twist q hq a)) (hone : ψ 1 = 1)
    (s : Finset M) :
    ∀ x : GasWord M, x.raise = x.lower → x.raise.support ⊆ s →
      ψ (MonoidAlgebra.single x 1) = zprod q (natToInt x.raise) := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro x hdiag hsub
    have hraise : x.raise = 0 :=
      Finsupp.support_eq_empty.mp (Finset.subset_empty.mp hsub)
    have hx : x = 1 := by
      refine GasWord.ext hraise ?_
      rw [← hdiag, hraise]
      rfl
    have hz : natToInt (0 : M →₀ ℕ) = 0 := by
      refine Finsupp.ext fun j => ?_
      simp
    rw [hx, one_raise, hz, zprod_zero, ← MonoidAlgebra.one_def]
    exact hone
  | insert i s hi ih =>
    intro x hdiag hsub
    have hzdiag : (erase i x).raise = (erase i x).lower := by
      rw [erase_raise, erase_lower, hdiag]
    have hzsub : (erase i x).raise.support ⊆ s := by
      rw [erase_raise, Finsupp.support_erase]
      intro j hj
      have hj' := Finset.mem_erase.mp hj
      rcases Finset.mem_insert.mp (hsub hj'.2) with h | h
      · exact absurd h hj'.1
      · exact h
    have hzi1 : (erase i x).raise i = 0 := by
      rw [erase_raise, Finsupp.erase_same]
    have hzi2 : (erase i x).lower i = 0 := by
      rw [erase_lower, Finsupp.erase_same]
    have hva : (gasV i : GasAlgebra M) ^ x.raise i * MonoidAlgebra.single (erase i x) 1
        = MonoidAlgebra.single (erase i x) 1 * gasV i ^ x.raise i := by
      rw [gasV_pow, single_mul_single_one, single_mul_single_one, gen_pow_eq_block]
      congr 1
      exact block_comm_disjoint (x.raise i) 0 hzi1 hzi2
    have hstep := kms_diagonal_step ψ (twist q hq) hexch (twist_gasV q hq i)
      (gasW_mul_gasV i) hva
    have hxeq : (gasV i : GasAlgebra M) ^ x.raise i * gasW i ^ x.raise i
        * MonoidAlgebra.single (erase i x) 1 = MonoidAlgebra.single x 1 := by
      rw [gasV_pow, gasW_pow, single_mul_single_one, single_mul_single_one, ← block_eq]
      congr 1
      have hlow : x.lower i = x.raise i := by rw [hdiag]
      conv_rhs => rw [eq_block_mul_erase i x]
      rw [hlow]
    rw [hxeq] at hstep
    rw [hstep, ih (erase i x) hzdiag hzsub, erase_raise,
      zprod_natToInt_erase q hq x.raise i]

/-! ## The uniqueness theorem -/

/-- **Theorem 4.1, uniqueness on monomials.**  Every normalised functional satisfying the exchange
identity takes the Gibbs value on every monomial. -/
theorem gas_kms_unique_single (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (hqlt : ∀ i, ‖q i‖ < 1)
    (hexch : ∀ a b : GasAlgebra M, ψ (a * b) = ψ (b * twist q hq a)) (hone : ψ 1 = 1)
    (x : GasWord M) :
    ψ (MonoidAlgebra.single x 1) = gibbsWeight q x := by
  classical
  by_cases hdiag : x.raise = x.lower
  · rw [gibbsWeight_of_diag hdiag]
    exact gas_diag_value ψ q hq hexch hone x.raise.support x hdiag (le_refl _)
  · rw [gibbsWeight_of_not_diag hdiag]
    obtain ⟨i, hi⟩ : ∃ i, x.raise i ≠ x.lower i := by
      by_contra hcon
      push Not at hcon
      exact hdiag (Finsupp.ext hcon)
    have hzi1 : (erase i x).raise i = 0 := by rw [erase_raise, Finsupp.erase_same]
    have hzi2 : (erase i x).lower i = 0 := by rw [erase_lower, Finsupp.erase_same]
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · have hb : x.lower i = x.raise i + (x.lower i - x.raise i) := by omega
      have hx : x = block i (x.raise i) (x.raise i + (x.lower i - x.raise i)) * erase i x := by
        conv_lhs => rw [eq_block_mul_erase i x]
        rw [← hb]
      rw [hx]
      exact gas_offdiag_neg ψ q hq hqlt hexch i (by omega) (x.raise i) (erase i x) hzi1 hzi2
    · have hb : x.raise i = x.lower i + (x.raise i - x.lower i) := by omega
      have hx : x = block i (x.lower i + (x.raise i - x.lower i)) (x.lower i) * erase i x := by
        conv_lhs => rw [eq_block_mul_erase i x]
        rw [← hb]
      rw [hx]
      exact gas_offdiag_pos ψ q hq hqlt hexch i (by omega) (x.lower i) (erase i x) hzi1 hzi2

/-- **Theorem 4.1, uniqueness.**  The Gibbs functional is the only normalised functional satisfying
the KMS exchange identity on the gas algebra. -/
theorem gas_kms_unique (q : M → ℂ) (hq : ∀ i, q i ≠ 0) (hqlt : ∀ i, ‖q i‖ < 1)
    (hexch : ∀ a b : GasAlgebra M, ψ (a * b) = ψ (b * twist q hq a)) (hone : ψ 1 = 1) :
    ψ = gibbs q := by
  classical
  refine LinearMap.ext fun a => ?_
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single x c =>
    rw [gas_apply_single ψ x c, gibbs_single,
      gas_kms_unique_single ψ q hq hqlt hexch hone x]

end GaloisForLFunctions.HTGeometry
