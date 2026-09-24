import GaloisForLFunctions.RHTower.EulerDeletionAllShiftLcmPolarity
import GaloisForLFunctions.RHTower.EulerDeletionTruncatedDivisorPairCorrelation

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped BigOperators

namespace RHTower

private def avgResidue (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ a ∈ range n, f (a + 1)) / (n : ℝ)

private theorem avgResidue_sum {α : Type*} [DecidableEq α]
    (n : ℕ) (S : Finset α) (f : α → ℕ → ℝ) :
    avgResidue n (fun k => ∑ i ∈ S, f i k) =
      ∑ i ∈ S, avgResidue n (f i) := by
  unfold avgResidue
  rw [Finset.sum_comm, Finset.sum_div]

private theorem avgResidue_sub (n : ℕ) (f g : ℕ → ℝ) :
    avgResidue n (fun k => f k - g k) =
      avgResidue n f - avgResidue n g := by
  simp [avgResidue, Finset.sum_sub_distrib, sub_div]

private theorem avgResidue_const (n : ℕ) (c : ℝ) (hn : 0 < n) :
    avgResidue n (fun _ => c) = c := by
  simp [avgResidue, hn.ne']

private theorem avgResidue_mul_const (n : ℕ) (f : ℕ → ℝ) (c : ℝ) :
    avgResidue n (fun k => f k * c) = avgResidue n f * c := by
  unfold avgResidue
  change (∑ a ∈ range n, f (a + 1) * c) / (n : ℝ) =
    (∑ a ∈ range n, f (a + 1)) / (n : ℝ) * c
  rw [← Finset.sum_mul]
  ring

private theorem avgResidue_const_mul (n : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    avgResidue n (fun k => c * f k) = c * avgResidue n f := by
  unfold avgResidue
  change (∑ a ∈ range n, c * f (a + 1)) / (n : ℝ) =
    c * ((∑ a ∈ range n, f (a + 1)) / (n : ℝ))
  rw [← Finset.mul_sum]
  ring

private def divisorIndicator (d k : ℕ) : ℝ := if d ∣ k then 1 else 0

private def centeredDivisorIndicator (n d k : ℕ) : ℝ :=
  divisorIndicator d k - avgResidue n (divisorIndicator d)

private theorem divisorIndicator_mean_eq_inv {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdn : d ∣ n) :
    avgResidue n (divisorIndicator d) = (d : ℝ)⁻¹ := by
  have hcard :
      (∑ a ∈ range n, divisorIndicator d (a + 1)) = ((n / d : ℕ) : ℝ) := by
    rw [show (∑ a ∈ range n, divisorIndicator d (a + 1)) =
        ((#{a ∈ range n | d ∣ a + 1} : ℕ) : ℝ) by
      simp [divisorIndicator]]
    exact_mod_cast Nat.card_multiples n d
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [avgResidue, hcard, Nat.cast_div hdn hdR]
  field_simp [hnR, hdR]

private theorem shiftedLcmFibre_eq_indicator_sum (n k m : ℕ) :
    shiftedLcmFibre n k m =
      ∑ de ∈ (n.divisors ×ˢ n.divisors).filter (fun de => Nat.lcm de.1 de.2 = n),
        ((moebius de.1 : ℤ) : ℝ) * ((moebius de.2 : ℤ) : ℝ) *
          divisorIndicator de.1 k * divisorIndicator de.2 m := by
  unfold shiftedLcmFibre
  apply Finset.sum_congr rfl
  intro de hde
  by_cases hd : de.1 ∣ k <;> by_cases he : de.2 ∣ m <;>
    simp [divisorIndicator, hd, he]

private def centeredLcmFibre (n k m : ℕ) : ℝ :=
  ∑ de ∈ (n.divisors ×ˢ n.divisors).filter (fun de => Nat.lcm de.1 de.2 = n),
    ((moebius de.1 : ℤ) : ℝ) * ((moebius de.2 : ℤ) : ℝ) *
      centeredDivisorIndicator n de.1 k * centeredDivisorIndicator n de.2 m

private theorem centeredLcmFibre_eq_doubleCenter (n k m : ℕ) :
    centeredLcmFibre n k m =
      shiftedLcmFibre n k m -
      avgResidue n (fun a => shiftedLcmFibre n a m) -
      avgResidue n (fun b => shiftedLcmFibre n k b) +
      avgResidue n (fun a => avgResidue n (fun b => shiftedLcmFibre n a b)) := by
  let S := (n.divisors ×ˢ n.divisors).filter (fun de => Nat.lcm de.1 de.2 = n)
  let c : ℕ × ℕ → ℝ := fun de =>
    ((moebius de.1 : ℤ) : ℝ) * ((moebius de.2 : ℤ) : ℝ)
  let u : ℕ × ℕ → ℕ → ℝ := fun de a => divisorIndicator de.1 a
  let v : ℕ × ℕ → ℕ → ℝ := fun de b => divisorIndicator de.2 b
  have hraw (a b : ℕ) : shiftedLcmFibre n a b =
      ∑ de ∈ S, c de * u de a * v de b :=
    shiftedLcmFibre_eq_indicator_sum n a b
  have hfirst : avgResidue n (fun a => shiftedLcmFibre n a m) =
      ∑ de ∈ S, c de * avgResidue n (u de) * v de m := by
    simp_rw [hraw]
    rw [avgResidue_sum]
    apply Finset.sum_congr rfl
    intro de hde
    rw [avgResidue_mul_const, avgResidue_const_mul]
  have hsecond : avgResidue n (fun b => shiftedLcmFibre n k b) =
      ∑ de ∈ S, c de * u de k * avgResidue n (v de) := by
    simp_rw [hraw]
    rw [avgResidue_sum]
    apply Finset.sum_congr rfl
    intro de hde
    rw [avgResidue_const_mul]
  have hdouble : avgResidue n (fun a => avgResidue n
      (fun b => shiftedLcmFibre n a b)) =
      ∑ de ∈ S, c de * avgResidue n (u de) * avgResidue n (v de) := by
    have hinner (a : ℕ) : avgResidue n (fun b => shiftedLcmFibre n a b) =
        ∑ de ∈ S, c de * u de a * avgResidue n (v de) := by
      simp_rw [hraw]
      rw [avgResidue_sum]
      apply Finset.sum_congr rfl
      intro de hde
      rw [avgResidue_const_mul]
    simp_rw [hinner]
    rw [avgResidue_sum]
    apply Finset.sum_congr rfl
    intro de hde
    rw [avgResidue_mul_const, avgResidue_const_mul]
  rw [hraw, hfirst, hsecond, hdouble]
  unfold centeredLcmFibre centeredDivisorIndicator
  change (∑ de ∈ S,
    c de * (u de k - avgResidue n (u de)) *
      (v de m - avgResidue n (v de))) = _
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro de hde
  ring

private theorem shiftedLcmFibre_eq_mu_indicator (n k m : ℕ) :
    shiftedLcmFibre n k m =
      ((moebius n : ℤ) : ℝ) * divisorIndicator n (k * m) := by
  rw [shiftedLcmFibre_eq_moebius_indicator_all]
  by_cases h : n ∣ k * m <;> simp [divisorIndicator, h]

theorem centeredLcmFibre_eq_doubleCentered_productIncidence (n k m : ℕ) :
    centeredLcmFibre n k m =
      ((moebius n : ℤ) : ℝ) *
        (divisorIndicator n (k * m) -
          avgResidue n (fun a => divisorIndicator n (a * m)) -
          avgResidue n (fun b => divisorIndicator n (k * b)) +
          avgResidue n (fun a => avgResidue n
            (fun b => divisorIndicator n (a * b)))) := by
  rw [centeredLcmFibre_eq_doubleCenter]
  simp_rw [shiftedLcmFibre_eq_mu_indicator]
  simp_rw [avgResidue_const_mul]
  ring

theorem divisorWindowDiscrepancy_eq_neg_centeredIncidence_sum
    {n d : ℕ} (t H : ℕ) (hn : 0 < n) (hd : 0 < d) (hdn : d ∣ n) :
    DeletionResidueMartingale.divisorWindowDiscrepancy d t H =
      -∑ k ∈ Ioc t (t + H), centeredDivisorIndicator n d k := by
  have hmean := divisorIndicator_mean_eq_inv hn hd hdn
  have hcount : (∑ k ∈ Ioc t (t + H), divisorIndicator d k) =
      ((#{k ∈ Ioc t (t + H) | d ∣ k} : ℕ) : ℝ) := by
    simp [divisorIndicator]
  have hsize : (Ioc t (t + H)).card = H := by simp [Nat.card_Ioc]
  unfold centeredDivisorIndicator
    DeletionResidueMartingale.divisorWindowDiscrepancy
  simp only [hmean, Finset.sum_sub_distrib, hcount]
  simp [hsize, div_eq_mul_inv]
  ring

def physicalCenteredLcmFibre (n t H u J : ℕ) : ℝ :=
  ∑ de ∈ (n.divisors ×ˢ n.divisors).filter (fun de => Nat.lcm de.1 de.2 = n),
    ((moebius de.1 : ℤ) : ℝ) * ((moebius de.2 : ℤ) : ℝ) *
      DeletionResidueMartingale.divisorWindowDiscrepancy de.1 t H *
      DeletionResidueMartingale.divisorWindowDiscrepancy de.2 u J

theorem physicalCenteredLcmFibre_eq_doubleCentered_windows
    (n t H u J : ℕ) (hn : 0 < n) :
    physicalCenteredLcmFibre n t H u J =
      ∑ k ∈ Ioc t (t + H), ∑ m ∈ Ioc u (u + J),
        centeredLcmFibre n k m := by
  classical
  let P := (n.divisors ×ˢ n.divisors).filter (fun de => Nat.lcm de.1 de.2 = n)
  have hbridge (de : ℕ × ℕ) (hde : de ∈ P) :
      DeletionResidueMartingale.divisorWindowDiscrepancy de.1 t H =
        -∑ k ∈ Ioc t (t + H), centeredDivisorIndicator n de.1 k ∧
      DeletionResidueMartingale.divisorWindowDiscrepancy de.2 u J =
        -∑ m ∈ Ioc u (u + J), centeredDivisorIndicator n de.2 m := by
    obtain ⟨hd, he⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hde).1
    exact ⟨divisorWindowDiscrepancy_eq_neg_centeredIncidence_sum t H hn
      (Nat.pos_of_mem_divisors hd) (Nat.dvd_of_mem_divisors hd),
      divisorWindowDiscrepancy_eq_neg_centeredIncidence_sum u J hn
        (Nat.pos_of_mem_divisors he) (Nat.dvd_of_mem_divisors he)⟩
  unfold physicalCenteredLcmFibre centeredLcmFibre
  change (∑ de ∈ P, _) = ∑ k ∈ Ioc t (t + H), ∑ m ∈ Ioc u (u + J),
    ∑ de ∈ P, _
  conv_lhs =>
    arg 2
    ext de
    rw [(hbridge de (by assumption)).1, (hbridge de (by assumption)).2]
  simp only [mul_neg, neg_mul, neg_neg]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro de hde
  ring

end RHTower
