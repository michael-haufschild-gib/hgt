import GaloisForLFunctions.ArithmeticOrientationTheory.FrustrationIndexControlsTheGroundEnergy
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.BalancedIncidenceIsLocallyPayable

/-!
# The lattice odd ledger is balanced

The odd Weil ledger sampled at the **logarithms of integers** `n ≥ 2` has no frustration at any
aperture: every overlap is aligned (`oddFold_lattice_nonpos`), so the form is balanced, its
frustration index is `0` (`frustrationIndex_lattice_eq_zero`), and its positivity is local
payment (`nonneg_iff_locallyPayable_lattice`).  The reason is tower locality: a prime-sum pair of
lattice positions `(log p^i, log p^j)` is also a prime-difference pair, and the difference carries
the larger prime weight, `Λ(p^{i+j})/√p^{i+j} ≤ Λ(p^{|i−j|})/√p^{|i−j|}`
(`primeKernel_log_add_le`), while the archimedean–polar weight is nonincreasing.

Together with the prime triangle (`frustrationIndex_primeTriangle`: index `2` at half-integer
log positions), this locates the frustration of the odd Weil ledger exactly: it is a continuum
phenomenon, absent on the lattice at every aperture and present between lattice points.

For arbitrary positive positions the frustrating couplings are bounded by the prime-sum charge
`β Λ(n) n^{−1/2}` alone (`oddFold_le_primeKernel`), so the frustration mass is at most `β` times
the prime-sum charge of the configuration (`frustrationMass_le_primeSumCharge`).
-/

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The prime kernel on the lattice -/

/-- At `log n` the prime kernel is `Λ(n)/√n`. -/
theorem primeKernel_log_nat {n : ℕ} (hn : 1 ≤ n) :
    primeKernel (Real.log n) = Λ n / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  unfold primeKernel
  rw [abs_of_nonneg hlog, Real.exp_log hn0, tsum_eq_single n fun m hm => if_neg fun h =>
    hm (by exact_mod_cast h.symm), if_pos rfl]

theorem div_le_div_of_le_denom {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (hcb : c ≤ b) :
    a / b ≤ a / c := by
  rw [div_le_div_iff₀ (lt_of_lt_of_le hc hcb) hc]
  nlinarith

/-- **Tower comparison**: within the tower of `r`, the prime weight at the sum of two positions
is at most the weight at their difference, `Λ(r^{i+j})/√r^{i+j} ≤ Λ(r^{i−j})/√r^{i−j}`. -/
theorem primeKernel_tower_le {r i j : ℕ} (hr : r.Prime) (hij : j < i) :
    primeKernel (Real.log ((r ^ i : ℕ) : ℝ) + Real.log ((r ^ j : ℕ) : ℝ)) ≤
      primeKernel (Real.log ((r ^ i : ℕ) : ℝ) - Real.log ((r ^ j : ℕ) : ℝ)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have h1 : Real.log ((r ^ i : ℕ) : ℝ) + Real.log ((r ^ j : ℕ) : ℝ) =
      Real.log ((r ^ (i + j) : ℕ) : ℝ) := by
    push_cast
    rw [pow_add, Real.log_mul (by positivity) (by positivity)]
  have h2 : Real.log ((r ^ i : ℕ) : ℝ) - Real.log ((r ^ j : ℕ) : ℝ) =
      Real.log ((r ^ (i - j) : ℕ) : ℝ) := by
    push_cast
    rw [← Real.log_div (by positivity) (by positivity), pow_sub₀ _ hr0.ne' hij.le, div_eq_mul_inv]
  rw [h1, h2, primeKernel_log_nat (Nat.one_le_pow _ _ hr.pos),
    primeKernel_log_nat (Nat.one_le_pow _ _ hr.pos), vonMangoldt_apply_pow (by omega),
    vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hr]
  have hlog : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr.one_lt.le)
  apply div_le_div_of_le_denom hlog (Real.sqrt_pos.2 (Nat.cast_pos.2 (pow_pos hr.pos _)))
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.pow_le_pow_right hr.pos (by omega)

/-- **The prime weight at a lattice sum is at most the weight at the lattice difference.** -/
theorem primeKernel_log_add_le {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a ≠ b) :
    primeKernel (Real.log a + Real.log b) ≤ primeKernel (Real.log a - Real.log b) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  by_cases hΛ : Λ (a * b) = 0
  · have h0 : primeKernel (Real.log a + Real.log b) = 0 := by
      rw [← Real.log_mul ha0.ne' hb0.ne', ← Nat.cast_mul,
        primeKernel_log_nat (by nlinarith), hΛ, zero_div]
    rw [h0]
    exact primeKernel_nonneg _
  · obtain ⟨r, k, hr, -, hrk⟩ := (isPrimePow_nat_iff _).1 (vonMangoldt_ne_zero_iff.1 hΛ)
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hr).1 (Dvd.intro b hrk.symm)
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hr).1 (Dvd.intro_left _ hrk.symm)
    have hij : i ≠ j := fun h => hab (by rw [h])
    rcases lt_or_gt_of_ne hij with h | h
    · have key := primeKernel_tower_le hr h
      have hR : primeKernel (Real.log ((r ^ i : ℕ) : ℝ) - Real.log ((r ^ j : ℕ) : ℝ)) =
          primeKernel (Real.log ((r ^ j : ℕ) : ℝ) - Real.log ((r ^ i : ℕ) : ℝ)) := by
        rw [← primeKernel_neg, neg_sub]
      rw [add_comm, hR]
      exact key
    · exact primeKernel_tower_le hr h

/-! ### Balance on the lattice -/

/-- **Every overlap of the lattice odd ledger is aligned.** -/
theorem oddFold_lattice_nonpos {n : ι → ℕ} (hn : ∀ x, 2 ≤ n x) (hinj : Function.Injective n)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (b : ι → ℝ) :
    HasNonpositiveOverlaps (oddFold (fun x => Real.log (n x : ℝ)) (weilLedgerKernel α β) b) := by
  intro x y hxy
  rw [oddFold_offDiag hxy]
  unfold weilLedgerKernel
  have hne : n x ≠ n y := fun h => hxy (hinj h)
  have hx0 : (0 : ℝ) < n x := by exact_mod_cast (by have := hn x; omega : 0 < n x)
  have hy0 : (0 : ℝ) < n y := by exact_mod_cast (by have := hn y; omega : 0 < n y)
  have hlx : 0 ≤ Real.log (n x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by have := hn x; omega : 1 ≤ n x))
  have hly : 0 ≤ Real.log (n y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by have := hn y; omega : 1 ≤ n y))
  have hlne : Real.log (n x : ℝ) ≠ Real.log (n y : ℝ) := fun h =>
    hne (by exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.2 hx0) (Set.mem_Ioi.2 hy0) h)
  have hd : 0 < |Real.log (n x : ℝ) - Real.log (n y : ℝ)| := abs_pos.2 (sub_ne_zero.2 hlne)
  have hle : |Real.log (n x : ℝ) - Real.log (n y : ℝ)| ≤
      |Real.log (n x : ℝ) + Real.log (n y : ℝ)| := by
    rw [abs_of_nonneg (add_nonneg hlx hly)]
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have hK := weilKernel_antitone hd hle
  have hprime := primeKernel_log_add_le (hn x) (hn y) hne
  nlinarith [mul_le_mul_of_nonneg_left hK hα, mul_le_mul_of_nonneg_left hprime hβ]

/-- **The lattice odd ledger is balanced at every aperture.** -/
theorem isBalanced_lattice {n : ι → ℕ} (hn : ∀ x, 2 ≤ n x) (hinj : Function.Injective n)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (b : ι → ℝ) :
    IsBalanced (oddFold (fun x => Real.log (n x : ℝ)) (weilLedgerKernel α β) b) :=
  isBalanced_of_aligned (oddFold_lattice_nonpos hn hinj hα hβ b)

/-- **The frustration index of the lattice odd ledger is zero.** -/
theorem frustrationIndex_lattice_eq_zero {n : ι → ℕ} (hn : ∀ x, 2 ≤ n x)
    (hinj : Function.Injective n) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (b : ι → ℝ) :
    frustrationIndex (oddFold (fun x => Real.log (n x : ℝ)) (weilLedgerKernel α β) b) = 0 :=
  (isBalanced_iff_frustrationIndex_eq_zero _).1 (isBalanced_lattice hn hinj hα hβ b)

/-- **On the lattice, positivity of the odd ledger is local payment.** -/
theorem nonneg_iff_locallyPayable_lattice {n : ι → ℕ} (hn : ∀ x, 2 ≤ n x)
    (hinj : Function.Injective n) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (b : ι → ℝ) :
    (∀ f : ι → ℝ, 0 ≤ incidenceEnergy
        (oddFold (fun x => Real.log (n x : ℝ)) (weilLedgerKernel α β) b) f) ↔
      LocallyPayable (oddFold (fun x => Real.log (n x : ℝ)) (weilLedgerKernel α β) b) :=
  nonneg_iff_locallyPayable_of_isBalanced (oddFold_isSymmetric (weilLedgerKernel_neg α β))
    (isBalanced_lattice hn hinj hα hβ b)

/-! ### The prime-sum charge bounds the frustration mass -/

omit [Fintype ι] in
/-- Every overlap of the odd ledger is at most the prime-sum charge `β · prime(p_x + p_y)`. -/
theorem oddFold_le_primeKernel {p : ι → ℝ} (hp : ∀ x, 0 < p x) (hinj : Function.Injective p)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (b : ι → ℝ) {x y : ι} (hxy : x ≠ y) :
    oddFold p (weilLedgerKernel α β) b x y ≤ β * primeKernel (p x + p y) := by
  rw [oddFold_offDiag hxy]
  unfold weilLedgerKernel
  have hd : 0 < |p x - p y| := abs_pos.2 (sub_ne_zero.2 fun h => hxy (hinj h))
  have hle : |p x - p y| ≤ |p x + p y| := by
    rw [abs_of_pos (add_pos (hp x) (hp y))]
    exact abs_sub_le_iff.2 ⟨by linarith [hp y], by linarith [hp x]⟩
  have hK := weilKernel_antitone hd hle
  have hpr := primeKernel_nonneg (p x - p y)
  nlinarith [mul_le_mul_of_nonneg_left hK hα, mul_nonneg hβ hpr]

/-- **The frustration mass is at most `β` times the prime-sum charge.** -/
theorem frustrationMass_le_primeSumCharge {p : ι → ℝ} (hp : ∀ x, 0 < p x)
    (hinj : Function.Injective p) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (b : ι → ℝ) :
    frustrationMass (oddFold p (weilLedgerKernel α β) b) ≤
      β * ∑ q ∈ primeSumPairs p, primeKernel (p q.1 + p q.2) := by
  set c := oddFold p (weilLedgerKernel α β) b with hc
  refine le_trans (frustrationMass_le isSignVector_one c) ?_
  rw [mul_sum]
  calc misalignedMass (fun _ => (1 : ℝ)) c
      ≤ ∑ i, ∑ j, (if (i, j) ∈ primeSumPairs p then β * primeKernel (p i + p j) else 0) := by
        unfold misalignedMass
        refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
        split_ifs with hP hmem hmem
        · rw [abs_of_pos (by simpa using hP.2)]
          exact oddFold_le_primeKernel hp hinj hα hβ b hP.1
        · exfalso
          apply hmem
          unfold primeSumPairs
          simp only [mem_filter, mem_univ, true_and]
          exact ⟨hP.1, oddFold_pos_imp_primeSum hp hinj hα hβ hP.1 (by simpa using hP.2)⟩
        · exact mul_nonneg hβ (primeKernel_nonneg _)
        · exact le_rfl
    _ = ∑ q ∈ primeSumPairs p, β * primeKernel (p q.1 + p q.2) := by
        rw [← Fintype.sum_prod_type', sum_ite_mem, univ_inter]

/-- On a prime-sum pair the charge is `Λ(n)/√n` for the integer `n = e^{p_x + p_y}`. -/
theorem primeKernel_eq_of_exp_eq {u : ℝ} {n : ℕ} (hn : 1 ≤ n) (h : Real.exp u = n) :
    primeKernel u = Λ n / Real.sqrt n := by
  have hu : u = Real.log n := by rw [← h, Real.log_exp]
  rw [hu, primeKernel_log_nat hn]

end

end GaloisForLFunctions.ArithmeticOrientationTheory
