import GaloisForLFunctions.RHTower.DirichletFamilyEndEffects

/-!
# Residue-class masses of the prime coefficients

For `a_n = Λ(n)/√n` and `A_r = ∑_{n ≤ X, n ≡ r (q)} a_n`:

* a residue class meets `(0, N]` in at most `N/q + 1` integers (`card_Ioc_residue_class_le`);
* by Cauchy–Schwarz in each class, `∑_{r mod q} A_r² ≤ (X/q + 1) ∑_{n ≤ X} a_n²` (`sum_classMass_sq_le`);
* the end-effect bracket of the family Frobenius bound is at most
  `7 q l² + 10 (X/q + 1) ∑ a_n²` (`sum_units_classMass_bracket_le`), and `A₁² ≤ π⁻² (X/q + 1) ∑ a_n²`
  (`oneClassMass_sq_le`).

The saving `1/q` in the class masses is what makes the end effects negligible up to `X ≤ q T^{1−δ}`.
-/

open Real Zeta23 Zeta23.PrimeSide

noncomputable section

namespace RHTower

/-- A residue class modulo `q` meets `(0, N]` in at most `N/q + 1` integers. -/
theorem card_Ioc_residue_class_le (q : ℕ) (N : ℕ) (r : ZMod q) :
    (((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod q) = r)).card : ℝ) ≤ N / q + 1 := by
  have h : ((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod q) = r)).card ≤ N / q + 1 := by
    calc ((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod q) = r)).card
        ≤ (Finset.range (N / q + 1)).card := by
          apply Finset.card_le_card_of_injOn (fun n => n / q)
          · intro n hn
            simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at hn
            simp only [Finset.coe_range, Set.mem_Iio]
            exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.2)
          · intro a ha b hb hab
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
            have hmod : a % q = b % q := (ZMod.natCast_eq_natCast_iff' a b q).mp (ha.2.trans hb.2.symm)
            have hab' : a / q = b / q := hab
            rw [← Nat.div_add_mod a q, ← Nat.div_add_mod b q, hmod, hab']
      _ = N / q + 1 := Finset.card_range _
  have h' : (((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod q) = r)).card : ℝ) ≤ ((N / q : ℕ) : ℝ) + 1 := by
    exact_mod_cast h
  have h2 : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q := Nat.cast_div_le
  linarith

theorem classMass_eq_filter (q : ℕ) (X : ℝ) (r : ZMod q) :
    classMass q X r = ∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r), acoef n := by
  unfold classMass classCoef
  rw [Finset.sum_filter]

/-- **Cauchy–Schwarz in one residue class.** -/
theorem classMass_sq_le {q : ℕ} {X : ℝ} (hX : 0 ≤ X) (r : ZMod q) :
    classMass q X r ^ 2 ≤ (X / q + 1) * ∑ n ∈ primeRange X, classCoef q r n ^ 2 := by
  rw [classMass_eq_filter]
  refine sq_sum_le_card_mul_sum_sq.trans ?_
  have hcard := card_Ioc_residue_class_le q ⌊X⌋₊ r
  have hfl : (⌊X⌋₊ : ℝ) / q ≤ X / q :=
    div_le_div_of_nonneg_right (Nat.floor_le hX) (by positivity)
  have hsum : ∑ n ∈ (primeRange X).filter (fun n : ℕ => (n : ZMod q) = r), acoef n ^ 2
      = ∑ n ∈ primeRange X, classCoef q r n ^ 2 := by
    unfold classCoef
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> simp
  rw [hsum]
  have h0 : 0 ≤ ∑ n ∈ primeRange X, classCoef q r n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  exact mul_le_mul_of_nonneg_right (by unfold primeRange; linarith) h0

/-- **The residue-class masses in mean square.** -/
theorem sum_classMass_sq_le {q : ℕ} [NeZero q] {X : ℝ} (hX : 0 ≤ X) :
    ∑ r : ZMod q, classMass q X r ^ 2 ≤ (X / q + 1) * ∑ n ∈ primeRange X, acoef n ^ 2 := by
  calc ∑ r : ZMod q, classMass q X r ^ 2
      ≤ ∑ r : ZMod q, (X / q + 1) * ∑ n ∈ primeRange X, classCoef q r n ^ 2 :=
        Finset.sum_le_sum fun r _ => classMass_sq_le hX r
    _ = (X / q + 1) * ∑ n ∈ primeRange X, ∑ r : ZMod q, classCoef q r n ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (X / q + 1) * ∑ n ∈ primeRange X, acoef n ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        unfold classCoef
        have e : ∀ r : ZMod q, (if (n : ZMod q) = r then acoef n else 0) ^ 2
            = if (n : ZMod q) = r then acoef n ^ 2 else 0 := fun r => by split_ifs <;> simp
        simp_rw [e]
        rw [Finset.sum_ite_eq]
        simp

theorem inv_injOn_units (q : ℕ) [NeZero q] :
    Set.InjOn (fun r : ZMod q => r⁻¹) ↑((Finset.univ : Finset (ZMod q)).filter IsUnit) := by
  intro r hr s hs h
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hr hs
  have h' : r⁻¹ = s⁻¹ := h
  calc r = r * (s⁻¹ * s) := by rw [ZMod.inv_mul_of_unit s hs, mul_one]
    _ = r * (r⁻¹ * s) := by rw [h']
    _ = (r * r⁻¹) * s := by ring
    _ = s := by rw [ZMod.mul_inv_of_unit r hr, one_mul]

/-- **The end-effect bracket.** -/
theorem sum_units_classMass_bracket_le {q : ℕ} [NeZero q] {X : ℝ} (hX : 0 ≤ X) (l : ℝ) :
    ∑ r ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
        (2 * (l + classMass q X r) ^ 2 + (l + classMass q X r + classMass q X r⁻¹) ^ 2)
      ≤ 7 * q * l ^ 2 + 10 * ((X / q + 1) * ∑ n ∈ primeRange X, acoef n ^ 2) := by
  set U := (Finset.univ : Finset (ZMod q)).filter IsUnit with hU
  set S := ∑ r : ZMod q, classMass q X r ^ 2 with hS
  have hpt : ∀ r ∈ U, 2 * (l + classMass q X r) ^ 2 + (l + classMass q X r + classMass q X r⁻¹) ^ 2
      ≤ 7 * l ^ 2 + 7 * classMass q X r ^ 2 + 3 * classMass q X r⁻¹ ^ 2 := fun r _ => by
    nlinarith [sq_nonneg (l - classMass q X r), sq_nonneg (l - classMass q X r⁻¹),
      sq_nonneg (classMass q X r - classMass q X r⁻¹)]
  have hcardU : (U.card : ℝ) ≤ q := by
    have : U.card ≤ (Finset.univ : Finset (ZMod q)).card := Finset.card_filter_le _ _
    rw [Finset.card_univ, ZMod.card] at this
    exact_mod_cast this
  have h1 : ∑ r ∈ U, classMass q X r ^ 2 ≤ S :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun r _ _ => sq_nonneg _
  have h2 : ∑ r ∈ U, classMass q X r⁻¹ ^ 2 ≤ S := by
    rw [← Finset.sum_image (f := fun r => classMass q X r ^ 2) (inv_injOn_units q)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun r _ _ => sq_nonneg _
  have hSle := sum_classMass_sq_le (q := q) hX
  calc ∑ r ∈ U, (2 * (l + classMass q X r) ^ 2 + (l + classMass q X r + classMass q X r⁻¹) ^ 2)
      ≤ ∑ r ∈ U, (7 * l ^ 2 + 7 * classMass q X r ^ 2 + 3 * classMass q X r⁻¹ ^ 2) :=
        Finset.sum_le_sum hpt
    _ = U.card * (7 * l ^ 2) + 7 * ∑ r ∈ U, classMass q X r ^ 2
          + 3 * ∑ r ∈ U, classMass q X r⁻¹ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          Finset.mul_sum, Finset.mul_sum]
    _ ≤ q * (7 * l ^ 2) + 7 * S + 3 * S := by
        have := mul_le_mul_of_nonneg_right hcardU (by positivity : (0:ℝ) ≤ 7 * l ^ 2)
        linarith
    _ ≤ 7 * q * l ^ 2 + 10 * ((X / q + 1) * ∑ n ∈ primeRange X, acoef n ^ 2) := by
        nlinarith

/-- `A₁ = π⁻¹ A_{1 mod q}`, so `A₁² ≤ π⁻² (X/q + 1) ∑ a_n²`. -/
theorem oneClassMass_sq_le {q : ℕ} [NeZero q] {X : ℝ} (hX : 0 ≤ X) :
    oneClassMass q X ^ 2 ≤ (X / q + 1) * ∑ n ∈ primeRange X, acoef n ^ 2 := by
  have e : oneClassMass q X = (1 / π) * classMass q X 1 := by
    unfold oneClassMass oneClassCoef classMass classCoef
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hpi : 0 < 1 / π := by positivity
    split_ifs with h
    · rw [mul_one, abs_mul, abs_neg, abs_of_pos hpi, abs_of_nonneg (acoef_nonneg n)]
    · simp
  have hcm := classMass_sq_le hX (1 : ZMod q)
  have hle : ∑ n ∈ primeRange X, classCoef q 1 n ^ 2 ≤ ∑ n ∈ primeRange X, acoef n ^ 2 :=
    Finset.sum_le_sum fun n _ => by unfold classCoef; split_ifs <;> simp [sq_nonneg]
  have hpi : (1 / π) ^ 2 ≤ 1 := by
    rw [div_pow, one_pow, div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hXq : 0 ≤ X / q + 1 := by positivity
  rw [e, mul_pow]
  calc (1 / π) ^ 2 * classMass q X 1 ^ 2 ≤ 1 * classMass q X 1 ^ 2 :=
        mul_le_mul_of_nonneg_right hpi (sq_nonneg _)
    _ ≤ (X / q + 1) * ∑ n ∈ primeRange X, acoef n ^ 2 := by
        rw [one_mul]; exact hcm.trans (mul_le_mul_of_nonneg_left hle hXq)

end RHTower
