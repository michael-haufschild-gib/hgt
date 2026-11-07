import GaloisForLFunctions.ArithmeticPositiveDuality.ADiscreteBeurlingOneOff
import GaloisForLFunctions.HTGeometry.OccupationEulerProduct

/-!
# Ordinary coefficients of integer-norm occupation products

Collect finite occupations by their ordinary integer norm. Absolute convergence makes each
fibre finite and identifies its cardinality with a natural Dirichlet coefficient. For prime
generator norms, coprime integers have independent occupation fibres.
-/

set_option autoImplicit false

open Complex Filter Topology
open scoped BigOperators
open GaloisForLFunctions.ArithmeticPositiveDuality.DiscreteOneOff

namespace GaloisForLFunctions.ArithmeticPositiveDuality.IntegerOccupation

noncomputable section

def norm (q : ℕ → ℕ) (v : ℕ →₀ ℕ) : ℕ := v.prod fun k m => q k ^ m

def coeff (q : ℕ → ℕ) (n : ℕ) : ℕ := Nat.card {v : ℕ →₀ ℕ // norm q v = n}

theorem norm_pos {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k) (v : ℕ →₀ ℕ) : 0 < norm q v := by
  classical
  unfold norm Finsupp.prod
  exact Finset.prod_pos fun k _ => pow_pos (lt_of_lt_of_le (by norm_num) (hq k)) _

@[simp] theorem norm_zero (q : ℕ → ℕ) : norm q 0 = 1 := by simp [norm]

theorem norm_add (q : ℕ → ℕ) (v w : ℕ →₀ ℕ) : norm q (v + w) = norm q v * norm q w := by
  classical
  exact Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _)

theorem dvd_norm_of_ne_zero {q : ℕ → ℕ} {v : ℕ →₀ ℕ} {k : ℕ} (hk : v k ≠ 0) :
    q k ∣ norm q v := by
  classical
  have hp : q k ∣ q k ^ v k := by
    cases he : v k with
    | zero => exact (hk he).elim
    | succ n => exact ⟨q k ^ n, by rw [pow_succ, Nat.mul_comm]⟩
  exact hp.trans (Finset.dvd_prod_of_mem (fun j => q j ^ v j) (Finsupp.mem_support_iff.mpr hk))

theorem norm_eq_one_iff {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k) (v : ℕ →₀ ℕ) :
    norm q v = 1 ↔ v = 0 := by
  constructor
  · intro hv
    ext k
    change v k = 0
    by_contra hk
    have hd : q k ∣ 1 := hv ▸ dvd_norm_of_ne_zero hk
    have hb := Nat.le_of_dvd (by norm_num : 0 < 1) hd
    have := hq k
    omega
  · rintro rfl
    exact norm_zero q

@[simp] theorem coeff_one {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k) : coeff q 1 = 1 := by
  letI : Unique {v : ℕ →₀ ℕ // norm q v = 1} :=
    { default := ⟨0, norm_zero q⟩
      uniq := fun v => Subtype.ext ((norm_eq_one_iff hq v.1).1 v.2) }
  exact Nat.card_unique

private def leftPart (q : ℕ → ℕ) (m : ℕ) (v : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.filter (fun k => q k ∣ m) v

private def rightPart (q : ℕ → ℕ) (m : ℕ) (v : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.filter (fun k => ¬q k ∣ m) v

private theorem parts_add (q : ℕ → ℕ) (m : ℕ) (v : ℕ →₀ ℕ) :
    leftPart q m v + rightPart q m v = v := by
  ext k
  by_cases hk : q k ∣ m <;>
    simp only [Finsupp.add_apply, leftPart, rightPart, Finsupp.filter_apply, hk,
      if_true, if_false, not_true_eq_false, not_false_eq_true, zero_add, add_zero]

/-- Prime labels in an occupation of a coprime product split into the two exact norms. -/
private theorem split_norm {q : ℕ → ℕ} (hq : ∀ k, (q k).Prime)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n)
    (v : ℕ →₀ ℕ) (hv : norm q v = m * n) :
    norm q (leftPart q m v) = m ∧ norm q (rightPart q m v) = n := by
  classical
  have hprod : norm q (leftPart q m v) * norm q (rightPart q m v) = m * n := by
    rw [← norm_add, parts_add, hv]
  have hleft : (norm q (leftPart q m v)).Coprime n := by
    apply Nat.coprime_prod_left_iff.2
    intro k hk
    have hkm : q k ∣ m := by
      by_contra he
      exact (Finsupp.mem_support_iff.mp hk) (by
        simp only [leftPart, Finsupp.filter_apply, if_neg he])
    exact (Nat.Coprime.of_dvd_left hkm hmn).pow_left _
  have hright : (norm q (rightPart q m v)).Coprime m := by
    apply Nat.coprime_prod_left_iff.2
    intro k hk
    have hkm : ¬q k ∣ m := by
      intro he
      exact (Finsupp.mem_support_iff.mp hk) (by
        simp only [rightPart, Finsupp.filter_apply, if_neg (not_not.mpr he)])
    exact ((hq k).coprime_iff_not_dvd.mpr hkm).pow_left _
  have hld : norm q (leftPart q m v) ∣ m :=
    hleft.dvd_mul_right.mp ⟨norm q (rightPart q m v), hprod.symm⟩
  have hrd : norm q (rightPart q m v) ∣ n :=
    hright.dvd_mul_left.mp ⟨norm q (leftPart q m v), by
      calc
        m * n = norm q (leftPart q m v) * norm q (rightPart q m v) := hprod.symm
        _ = norm q (rightPart q m v) * norm q (leftPart q m v) := Nat.mul_comm _ _⟩
  have hle := Nat.le_of_dvd hm hld
  have hre := Nat.le_of_dvd hn hrd
  have he : norm q (leftPart q m v) = m := by
    apply Nat.le_antisymm hle
    apply Nat.le_of_mul_le_mul_right (c := n) _ hn
    calc
      m * n = norm q (leftPart q m v) * norm q (rightPart q m v) := hprod.symm
      _ ≤ norm q (leftPart q m v) * n := Nat.mul_le_mul_left _ hre
  refine ⟨he, Nat.le_antisymm hre ?_⟩
  apply Nat.le_of_mul_le_mul_right (c := m) _ hm
  rw [he] at hprod
  exact (by simpa only [Nat.mul_comm] using hprod.symm.le)

private theorem parts_add_of_norm {q : ℕ → ℕ} (hq : ∀ k, (q k).Prime)
    {m n : ℕ} (hmn : m.Coprime n) {v w : ℕ →₀ ℕ}
    (hv : norm q v = m) (hw : norm q w = n) :
    leftPart q m (v + w) = v ∧ rightPart q m (v + w) = w := by
  have hvm (k : ℕ) (hk : ¬q k ∣ m) : v k = 0 := by
    by_contra he
    exact hk (hv ▸ dvd_norm_of_ne_zero he)
  have hwn (k : ℕ) (hk : q k ∣ m) : w k = 0 := by
    by_contra he
    have hd : q k ∣ n := hw ▸ dvd_norm_of_ne_zero he
    exact ((hq k).coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left hd hmn.symm)) hk
  constructor <;> ext k <;> by_cases hk : q k ∣ m
  · simp only [leftPart, Finsupp.filter_apply, if_pos hk, Finsupp.add_apply, hwn k hk,
      add_zero]
  · simp only [leftPart, Finsupp.filter_apply, if_neg hk, hvm k hk]
  · simp only [rightPart, Finsupp.filter_apply, if_neg (not_not.mpr hk), hwn k hk]
  · simp only [rightPart, Finsupp.filter_apply, if_pos hk, Finsupp.add_apply, hvm k hk,
      zero_add]

private def coprimeFiberEquiv {q : ℕ → ℕ} (hq : ∀ k, (q k).Prime)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    {v : ℕ →₀ ℕ // norm q v = m * n} ≃
      ({v : ℕ →₀ ℕ // norm q v = m} × {v : ℕ →₀ ℕ // norm q v = n}) where
  toFun v := (⟨leftPart q m v.1, (split_norm hq hm hn hmn v.1 v.2).1⟩,
    ⟨rightPart q m v.1, (split_norm hq hm hn hmn v.1 v.2).2⟩)
  invFun w := ⟨w.1.1 + w.2.1, by rw [norm_add, w.1.2, w.2.2]⟩
  left_inv v := Subtype.ext (parts_add q m v.1)
  right_inv w := Prod.ext (Subtype.ext (parts_add_of_norm hq hmn w.1.2 w.2.2).1)
    (Subtype.ext (parts_add_of_norm hq hmn w.1.2 w.2.2).2)

private def term (q : ℕ → ℕ) (s : ℂ) (v : ℕ →₀ ℕ) : ℂ :=
  cexp (-(s * Real.log (norm q v)))

private theorem term_eq {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k) (s : ℂ) (v : ℕ →₀ ℕ) :
    term q s v =
      _root_.HTGeometry.nomeMonomial (fun k => cexp (-(s * Real.log (q k)))) v := by
  classical
  have hlog : Real.log (norm q v) =
      ∑ k ∈ v.support, (v k : ℝ) * Real.log (q k) := by
    unfold norm Finsupp.prod
    push_cast
    rw [Real.log_prod (fun k _ => pow_ne_zero _ (by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (hq k)).ne'))]
    simp only [Real.log_pow]
  rw [term, hlog, _root_.HTGeometry.nomeMonomial, Finsupp.prod]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Complex.exp_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private theorem primeTerm_norm_lt {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k)
    {s : ℂ} (hs : 1 < s.re) (k : ℕ) : ‖cexp (-(s * Real.log (q k)))‖ < 1 := by
  rw [norm_cexp_neg_mul, Real.exp_lt_one_iff]
  have hp : 0 < Real.log (q k) := Real.log_pos (by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) (hq k)))
  nlinarith only [hs, hp]

private theorem summable_term_norm {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k)
    {s : ℂ} (hs : 1 < s.re)
    (hsum : Summable fun k => Real.exp (-(s.re * Real.log (q k)))) :
    Summable fun v => ‖term q s v‖ := by
  have h := (_root_.HTGeometry.summable_nomeMonomial_pow_iff 0
    (fun k => cexp (-(s * Real.log (q k)))) (primeTerm_norm_lt hq hs)).2 (by
      simpa only [zero_add, pow_one, norm_cexp_neg_mul] using hsum)
  simpa only [zero_add, pow_one, term_eq hq] using h

/-- Absolute convergence at one real argument makes every norm fibre finite. -/
theorem finite_norm_fiber {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k)
    (hsum : Summable fun k => Real.exp (-(2 * Real.log (q k)))) (n : ℕ) :
    Finite {v : ℕ →₀ ℕ // norm q v = n} := by
  have h := (summable_term_norm hq (s := 2) (by norm_num) (by simpa using hsum)).subtype
    (fun v => norm q v = n)
  have hc : Summable (fun _ : {v : ℕ →₀ ℕ // norm q v = n} =>
      Real.exp (-(2 * Real.log n))) := h.congr fun v => by
    change ‖cexp (-((2 : ℂ) * Real.log (norm q v.1)))‖ = _
    rw [v.2, norm_cexp_neg_mul]
    norm_num
  exact Finite.of_summable_const (Real.exp_pos _) hc

@[simp] theorem coeff_zero {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k) : coeff q 0 = 0 := by
  haveI : IsEmpty {v : ℕ →₀ ℕ // norm q v = 0} :=
    ⟨fun v => (norm_pos hq v.1).ne' v.2⟩
  simp [coeff]

/-- Repeated rational-prime labels still give ordinary multiplicative coefficients. -/
theorem coeff_mul_of_coprime {q : ℕ → ℕ} (hq : ∀ k, (q k).Prime)
    {m n : ℕ} (hmn : m.Coprime n) : coeff q (m * n) = coeff q m * coeff q n := by
  by_cases hm : m = 0
  · simp only [hm, zero_mul, coeff_zero (fun k => (hq k).two_le)]
  by_cases hn : n = 0
  · simp only [hn, mul_zero, coeff_zero (fun k => (hq k).two_le)]
  exact (Nat.card_congr (coprimeFiberEquiv hq (Nat.pos_of_ne_zero hm)
    (Nat.pos_of_ne_zero hn) hmn)).trans (Nat.card_prod _ _)

/-- Group the absolutely convergent occupation expansion by its integer norms. -/
theorem hasSum_coeff_exp {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k)
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * Real.log (q k))))
    {s F : ℂ} (hs : 1 < s.re)
    (hprod : HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) F) :
    HasSum (fun n => (coeff q n : ℂ) * cexp (-(s * Real.log n))) F := by
  have heq := (_root_.HTGeometry.hasProd_inv_one_sub_nome
    (fun k => cexp (-(s * Real.log (q k)))) (primeTerm_norm_lt hq hs)
    (by simpa only [norm_cexp_neg_mul] using hsum s.re hs)).unique hprod
  have hoc : HasSum (term q s) F := by
    rw [← heq]
    simpa only [term_eq hq] using (summable_term_norm hq hs (hsum s.re hs)).of_norm.hasSum
  have hfiber (n : ℕ) :
      (∑' v : {v : ℕ →₀ ℕ // norm q v = n}, term q s v.1) =
        (coeff q n : ℂ) * cexp (-(s * Real.log n)) := by
    letI := finite_norm_fiber hq (hsum 2 (by norm_num)) n
    letI := Fintype.ofFinite {v : ℕ →₀ ℕ // norm q v = n}
    have he (v : {v : ℕ →₀ ℕ // norm q v = n}) :
        term q s v.1 = cexp (-(s * Real.log n)) := by rw [term, v.2]
    simp only [he, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      coeff, Nat.card_eq_fintype_card]
  exact (hoc.tsum_fiberwise (norm q)).congr_fun fun n => (hfiber n).symm

/-- The occupation Euler product is an ordinary Dirichlet series with natural coefficients. -/
theorem hasSum_coeff {q : ℕ → ℕ} (hq : ∀ k, 2 ≤ q k)
    (hsum : ∀ a : ℝ, 1 < a → Summable fun k => Real.exp (-(a * Real.log (q k))))
    {s F : ℂ} (hs : 1 < s.re)
    (hprod : HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) F) :
    LSeriesHasSum (fun n => (coeff q n : ℂ)) s F := by
  have hc := hasSum_coeff_exp hq hsum hs hprod
  refine hc.congr_fun fun n => ?_
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term, coeff_zero hq]
  · have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
      simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
    rw [LSeries.term, if_neg hn, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn),
      hlog, div_eq_mul_inv, ← Complex.exp_neg]
    congr 2
    ring

end
end GaloisForLFunctions.ArithmeticPositiveDuality.IntegerOccupation
