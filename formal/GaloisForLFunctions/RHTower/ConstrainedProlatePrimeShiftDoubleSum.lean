import GaloisForLFunctions.RHTower.ConstrainedProlateExteriorWeil
import GaloisForLFunctions.RHTower.ArcsineZetaDerivativeSpectrum

/-!
# Double-sum prime-shift and divisor-reindexing identity for the prolate prime charge

This module formalises the double-sum identity connecting the prime-shift radial representation
with the divisor-reindexed logarithmic prime charge:
$$\sum_{q=2}^\infty \frac{\Lambda(q)}{q} \sum_{j=1}^\infty \frac{\arcsin(1/(qj))}{j} = \sum_{k=2}^\infty \frac{\log k}{k} \arcsin(1/k)$$
and identifies the resulting unsigned response constant with the arithmetic diagonal trace.
-/

open scoped BigOperators Nat
open GaloisForLFunctions

noncomputable section

namespace GaloisForLFunctions

/-- The 2D general term $\frac{\Lambda(q)}{q} \frac{\arcsin(1/(qj))}{j}$ for $q \ge 2, j \ge 1$,
and $0$ otherwise. -/
def primeShiftDoubleSumTerm (q j : ℕ) : ℝ :=
  if 2 ≤ q ∧ 1 ≤ j then
    (ArithmeticFunction.vonMangoldt q / (q : ℝ)) *
      (Real.arcsin (1 / ((q : ℝ) * (j : ℝ))) / (j : ℝ))
  else 0

theorem primeShiftDoubleSumTerm_eq (q j : ℕ) (hq : 2 ≤ q) (hj : 1 ≤ j) :
    primeShiftDoubleSumTerm q j =
      ArithmeticFunction.vonMangoldt q / ((q : ℝ) * (j : ℝ)) *
        Real.arcsin (1 / ((q : ℝ) * (j : ℝ))) := by
  unfold primeShiftDoubleSumTerm
  simp [hq, hj]
  ring

theorem primeShiftDoubleSumTerm_nonneg (q j : ℕ) : 0 ≤ primeShiftDoubleSumTerm q j := by
  unfold primeShiftDoubleSumTerm
  split_ifs with h
  · have hqpos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hjpos : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hqjpos : 0 < (q : ℝ) * (j : ℝ) := mul_pos hqpos hjpos
    have harc : 0 ≤ Real.arcsin (1 / ((q : ℝ) * (j : ℝ))) :=
      Real.arcsin_nonneg.mpr (by positivity)
    exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hqpos.le)
      (div_nonneg harc hjpos.le)
  · exact le_rfl

/-- The fiber sum over the antidiagonal divisor pairs $q j = n$ collapses by the von Mangoldt
divisor sum identity to the depth-$n$ prime series term. -/
theorem sum_divisorsAntidiagonal_primeShiftDoubleSumTerm (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ n.divisorsAntidiagonal, primeShiftDoubleSumTerm p.1 p.2 =
      constrainedProlatePrimeSeriesTerm (n - 2) := by
  rw [Nat.sum_divisorsAntidiagonal]
  have hn0 : n ≠ 0 := by omega
  have hsplit : (∑ q ∈ n.divisors, primeShiftDoubleSumTerm q (n / q)) =
      ∑ q ∈ n.divisors.filter (fun q => 2 ≤ q), primeShiftDoubleSumTerm q (n / q) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := n.divisors) (p := fun q => 2 ≤ q)]
    have hzero : ∑ q ∈ n.divisors.filter (fun q => ¬(2 ≤ q)), primeShiftDoubleSumTerm q (n / q) = 0 := by
      refine Finset.sum_eq_zero fun q hq => ?_
      rw [Finset.mem_filter, Nat.mem_divisors] at hq
      obtain ⟨⟨hqdvd, -⟩, hqnot⟩ := hq
      have hq1 : q = 1 := by
        have hqpos : 0 < q := Nat.pos_of_dvd_of_pos hqdvd (by omega)
        omega
      subst hq1
      unfold primeShiftDoubleSumTerm
      simp
    rw [hzero, add_zero]
  rw [hsplit]
  have hterm : ∀ q ∈ n.divisors.filter (fun q => 2 ≤ q),
      primeShiftDoubleSumTerm q (n / q) =
        ArithmeticFunction.vonMangoldt q * (Real.arcsin (1 / (n : ℝ)) / (n : ℝ)) := by
    intro q hq
    simp only [Finset.mem_filter, Nat.mem_divisors] at hq
    obtain ⟨⟨hqdvd, -⟩, hq2⟩ := hq
    have hqpos : 0 < q := by omega
    have hjpos : 1 ≤ n / q := by
      refine Nat.div_pos (Nat.le_of_dvd (by omega) hqdvd) hqpos
    have hmul : (q : ℝ) * ((n / q : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hqdvd]
    rw [primeShiftDoubleSumTerm_eq q (n / q) hq2 hjpos, hmul]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    constrainedProlate_sum_vonMangoldt_divisors_ge_two n]
  unfold constrainedProlatePrimeSeriesTerm
  have hnn : ((n - 2 + 2 : ℕ) : ℝ) = (n : ℝ) := by
    congr 1
    omega
  rw [hnn]
  ring

theorem sum_divisorsAntidiagonal_primeShiftDoubleSumTerm_zero :
    ∑ p ∈ (0 : ℕ).divisorsAntidiagonal, primeShiftDoubleSumTerm p.1 p.2 = 0 := by
  simp [Nat.divisorsAntidiagonal_zero]

theorem sum_divisorsAntidiagonal_primeShiftDoubleSumTerm_one :
    ∑ p ∈ (1 : ℕ).divisorsAntidiagonal, primeShiftDoubleSumTerm p.1 p.2 = 0 := by
  have hd1 : (1 : ℕ).divisorsAntidiagonal = {(1, 1)} := by decide
  rw [hd1, Finset.sum_singleton]
  unfold primeShiftDoubleSumTerm
  simp

/-- Product multiplication map on index pairs. -/
def prodMul (p : ℕ × ℕ) : ℕ := p.1 * p.2

theorem primeShiftDoubleSumTerm_eq_zero_of_prodMul_zero {p : ℕ × ℕ} (h : prodMul p = 0) :
    primeShiftDoubleSumTerm p.1 p.2 = 0 := by
  dsimp [prodMul] at h
  cases Nat.mul_eq_zero.mp h with
  | inl h1 => unfold primeShiftDoubleSumTerm; simp [h1]
  | inr h2 => unfold primeShiftDoubleSumTerm; simp [h2]

theorem tsum_fiber_eq_sum_divisorsAntidiagonal (n : ℕ) (hn : n ≠ 0) :
    (∑' p : {p : ℕ × ℕ // prodMul p = n}, primeShiftDoubleSumTerm p.1.1 p.1.2) =
      ∑ p ∈ n.divisorsAntidiagonal, primeShiftDoubleSumTerm p.1 p.2 := by
  let hequiv : {p : ℕ × ℕ // prodMul p = n} ≃ {p // p ∈ n.divisorsAntidiagonal} :=
    Equiv.subtypeEquiv (Equiv.refl (ℕ × ℕ)) (by simp [prodMul, Nat.mem_divisorsAntidiagonal, hn])
  have h := (hequiv.symm.tsum_eq (fun p => primeShiftDoubleSumTerm p.1.1 p.1.2))
  have hcomp : (fun c : {p // p ∈ n.divisorsAntidiagonal} => primeShiftDoubleSumTerm (hequiv.symm c).1.1 (hequiv.symm c).1.2) =
      (fun c : {p // p ∈ n.divisorsAntidiagonal} => primeShiftDoubleSumTerm c.1.1 c.1.2) := by
    ext ⟨p, hp⟩
    rfl
  rw [hcomp] at h
  rw [← h]
  rw [tsum_fintype]
  exact Finset.sum_coe_sort (n.divisorsAntidiagonal) (fun p => primeShiftDoubleSumTerm p.1 p.2)

theorem tsum_fiber_eq_sum_divisorsAntidiagonal_zero :
    (∑' p : {p : ℕ × ℕ // prodMul p = 0}, primeShiftDoubleSumTerm p.1.1 p.1.2) =
      ∑ p ∈ (0 : ℕ).divisorsAntidiagonal, primeShiftDoubleSumTerm p.1 p.2 := by
  have hzero : (fun p : {p : ℕ × ℕ // prodMul p = 0} => primeShiftDoubleSumTerm p.1.1 p.1.2) = fun _ => 0 := by
    ext p
    exact primeShiftDoubleSumTerm_eq_zero_of_prodMul_zero p.2
  rw [hzero, tsum_zero, sum_divisorsAntidiagonal_primeShiftDoubleSumTerm_zero]

theorem tsum_fiber_primeShiftDoubleSumTerm_eq (n : ℕ) :
    (∑' p : {p : ℕ × ℕ // prodMul p = n}, primeShiftDoubleSumTerm p.1.1 p.1.2) =
      if n < 2 then 0 else constrainedProlatePrimeSeriesTerm (n - 2) := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · rw [if_pos (by omega), tsum_fiber_eq_sum_divisorsAntidiagonal_zero,
        sum_divisorsAntidiagonal_primeShiftDoubleSumTerm_zero]
    · rw [if_pos (by omega), tsum_fiber_eq_sum_divisorsAntidiagonal 1 (by decide),
        sum_divisorsAntidiagonal_primeShiftDoubleSumTerm_one]
  · rw [if_neg (not_lt.mpr hn), tsum_fiber_eq_sum_divisorsAntidiagonal n (by omega),
      sum_divisorsAntidiagonal_primeShiftDoubleSumTerm n hn]

theorem summable_primeShiftDoubleSumTerm_fiber (n : ℕ) :
    Summable (fun p : {p : ℕ × ℕ // prodMul p = n} => primeShiftDoubleSumTerm p.1.1 p.1.2) := by
  by_cases hn : n = 0
  · refine summable_of_ne_finset_zero (s := ∅) ?_
    intro ⟨p, hp⟩ _
    exact primeShiftDoubleSumTerm_eq_zero_of_prodMul_zero (hn ▸ hp)
  · let hequiv : {p : ℕ × ℕ // prodMul p = n} ≃ {p // p ∈ n.divisorsAntidiagonal} :=
      Equiv.subtypeEquiv (Equiv.refl (ℕ × ℕ)) (by simp [prodMul, Nat.mem_divisorsAntidiagonal, hn])
    have hs : Summable (fun c : {p // p ∈ n.divisorsAntidiagonal} => primeShiftDoubleSumTerm c.1.1 c.1.2) :=
      (hasSum_fintype _).summable
    exact hequiv.symm.summable_iff.mp hs

theorem summable_shifted_primeSeries :
    Summable (fun n : ℕ => if n < 2 then 0 else constrainedProlatePrimeSeriesTerm (n - 2)) := by
  have hs : Summable (fun n : ℕ => constrainedProlatePrimeSeriesTerm n) :=
    summable_constrainedProlatePrimeSeriesTerm
  rw [← (summable_nat_add_iff 2)]
  have heq2 : (fun n : ℕ => if n + 2 < 2 then 0 else constrainedProlatePrimeSeriesTerm (n + 2 - 2)) =
      fun n => constrainedProlatePrimeSeriesTerm n := by
    ext n
    have : ¬(n + 2 < 2) := by omega
    simp [this]
  rw [heq2]
  exact hs

theorem tsum_shifted_primeSeries_eq :
    (∑' n : ℕ, if n < 2 then (0 : ℝ) else constrainedProlatePrimeSeriesTerm (n - 2)) =
      ∑' n : ℕ, constrainedProlatePrimeSeriesTerm n := by
  have h_add := summable_shifted_primeSeries.sum_add_tsum_nat_add 2
  have hhead : (∑ i ∈ Finset.range 2, (if i < 2 then (0 : ℝ) else constrainedProlatePrimeSeriesTerm (i - 2))) = 0 := by
    simp [Finset.sum_range_succ]
  rw [hhead, zero_add] at h_add
  rw [← h_add]
  apply tsum_congr
  intro n
  have : ¬(n + 2 < 2) := by omega
  simp [this]

theorem summable_tsum_primeShiftDoubleSumTerm_fiber :
    Summable (fun n : ℕ => ∑' p : {p : ℕ × ℕ // prodMul p = n}, primeShiftDoubleSumTerm p.1.1 p.1.2) := by
  have heq : (fun n : ℕ => ∑' p : {p : ℕ × ℕ // prodMul p = n}, primeShiftDoubleSumTerm p.1.1 p.1.2) =
      fun n => if n < 2 then 0 else constrainedProlatePrimeSeriesTerm (n - 2) := by
    ext n
    exact tsum_fiber_primeShiftDoubleSumTerm_eq n
  rw [heq]
  exact summable_shifted_primeSeries

/-- The fiber partition equivalence $(n, p) \mapsto p$. -/
def prodMulEquiv : (n : ℕ) × {p : ℕ × ℕ // prodMul p = n} ≃ ℕ × ℕ :=
  Equiv.sigmaFiberEquiv prodMul

/-- Absolute summability of the 2D prime-shift array. -/
theorem summable_primeShiftDoubleSumTerm_prod :
    Summable (fun p : ℕ × ℕ => primeShiftDoubleSumTerm p.1 p.2) := by
  have hequiv_sum : Summable ((fun p : ℕ × ℕ => primeShiftDoubleSumTerm p.1 p.2) ∘ prodMulEquiv) ↔
      Summable (fun p : ℕ × ℕ => primeShiftDoubleSumTerm p.1 p.2) := prodMulEquiv.summable_iff
  rw [← hequiv_sum]
  have hnonneg : ∀ x : (n : ℕ) × {p : ℕ × ℕ // prodMul p = n}, 0 ≤ ((fun p : ℕ × ℕ => primeShiftDoubleSumTerm p.1 p.2) ∘ prodMulEquiv) x := by
    intro ⟨n, p⟩
    exact primeShiftDoubleSumTerm_nonneg p.1.1 p.1.2
  rw [summable_sigma_of_nonneg hnonneg]
  refine ⟨fun n => ?_, ?_⟩
  · have hcomp : (fun y : {p // prodMul p = n} => ((fun p => primeShiftDoubleSumTerm p.1 p.2) ∘ prodMulEquiv) ⟨n, y⟩) =
        (fun y : {p // prodMul p = n} => primeShiftDoubleSumTerm y.1.1 y.1.2) := by
      ext y
      rfl
    rw [hcomp]
    exact summable_primeShiftDoubleSumTerm_fiber n
  · have hcomp : (fun x : ℕ => ∑' y, ((fun p => primeShiftDoubleSumTerm p.1 p.2) ∘ prodMulEquiv) ⟨x, y⟩) =
        (fun x => ∑' y : {p // prodMul p = x}, primeShiftDoubleSumTerm y.1.1 y.1.2) := by
      ext x
      rfl
    rw [hcomp]
    exact summable_tsum_primeShiftDoubleSumTerm_fiber

/-- Rearrangement lemma over multiplicative fibers. -/
theorem tsum_prodMul_fiber_decomposition (f : ℕ × ℕ → ℝ) (hf : Summable f) (g : ℕ → ℝ)
    (h : ∀ n, (∑' c : {p : ℕ × ℕ // prodMul p = n}, f c.1) = g n) :
    (∑' p : ℕ × ℕ, f p) = ∑' n, g n := by
  have he : (∑' p : ℕ × ℕ, f p) = ∑' (x : (n : ℕ) × {p // prodMul p = n}), f (prodMulEquiv x) :=
    (prodMulEquiv.tsum_eq f).symm
  rw [he]
  have hs : Summable (fun x : (n : ℕ) × {p // prodMul p = n} => f (prodMulEquiv x)) :=
    prodMulEquiv.summable_iff.mpr hf
  have hs_sig := hs.tsum_sigma
  change (∑' (p : (b : ℕ) × { c // prodMul c = b }), f (prodMulEquiv p)) =
    ∑' (b : ℕ) (c : { p // prodMul p = b }), f c.1 at hs_sig
  rw [hs_sig]
  apply tsum_congr
  intro n
  exact h n

/-- Unconditional double-sum Dirichlet divisor reindexing theorem for the prolate prime charge:
$$\sum_{q=2}^\infty \sum_{j=1}^\infty \frac{\Lambda(q)}{q} \frac{\arcsin(1/(qj))}{j} = \sum_{n=0}^\infty \frac{\log(n+2)}{n+2} \arcsin\left(\frac{1}{n+2}\right)$$
-/
theorem tsum_primeShiftDoubleSumTerm_eq_tsum_primeSeries :
    (∑' q : ℕ, ∑' j : ℕ, primeShiftDoubleSumTerm q j) =
      ∑' n : ℕ, constrainedProlatePrimeSeriesTerm n := by
  have hsum_prod := summable_primeShiftDoubleSumTerm_prod
  have hprod_comm : (∑' q : ℕ, ∑' j : ℕ, primeShiftDoubleSumTerm q j) =
      ∑' p : ℕ × ℕ, primeShiftDoubleSumTerm p.1 p.2 := by
    rw [← hsum_prod.tsum_prod]
  rw [hprod_comm]
  have hdecomp := tsum_prodMul_fiber_decomposition
    (fun p => primeShiftDoubleSumTerm p.1 p.2) hsum_prod
    (fun n => if n < 2 then 0 else constrainedProlatePrimeSeriesTerm (n - 2))
    tsum_fiber_primeShiftDoubleSumTerm_eq
  exact hdecomp.trans tsum_shifted_primeSeries_eq

/-- The unsigned response constant before divisor reindexing. -/
noncomputable def primeShiftUnsignedResponseConstant : ℝ :=
  (8 / (11 * Real.pi)) * (∑' q : ℕ, ∑' j : ℕ, primeShiftDoubleSumTerm q j)

/-- The unsigned response constant matches the prolate arcsine charge under the $8/(11\pi)$ scale. -/
theorem primeShiftUnsignedResponseConstant_eq_prolateArcsineCharge :
    primeShiftUnsignedResponseConstant =
      (8 / (11 * Real.pi)) * (∑' n : ℕ, constrainedProlatePrimeSeriesTerm n) := by
  unfold primeShiftUnsignedResponseConstant
  rw [tsum_primeShiftDoubleSumTerm_eq_tsum_primeSeries]

/-- The unsigned response constant is exactly $-1/2$ of the signed radial prime constant $\mathcal{D}_{\text{prime}}$. -/
theorem primeShiftUnsignedResponseConstant_eq_neg_half_primeConstant :
    primeShiftUnsignedResponseConstant = -(1 / 2) * constrainedProlatePrimeConstant := by
  rw [primeShiftUnsignedResponseConstant_eq_prolateArcsineCharge,
    constrainedProlatePrimeConstant]
  ring

/-- The unsigned response constant equals half of the total trace of the limiting arithmetic diagonal operator. -/
theorem primeShiftUnsignedResponseConstant_eq_half_arithmeticTrace :
    primeShiftUnsignedResponseConstant = (1 / 2) * (∑' n : ℕ, constrainedProlateArithmeticEigenvalue n) := by
  rw [primeShiftUnsignedResponseConstant_eq_neg_half_primeConstant,
    tsum_constrainedProlateArithmeticEigenvalue]
  ring

end GaloisForLFunctions
