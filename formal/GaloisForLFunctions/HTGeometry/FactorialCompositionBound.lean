import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The factorial entropy bound for a composition with no dominant part

If `n₁ + ⋯ + n_d = M` and every part is at most `M − R`, then the product of the factorials of the
parts loses a full binomial factor against `M!`:

`(∏ nᵢ!) · M^R ≤ 2^R · R! · M!`.

The mechanism is elementary and needs no Stirling estimate.  Writing `s = M − max nᵢ`, the
multinomial coefficient is at least `C(M, s)`, so `(∏ nᵢ!)·C(M,s) ≤ M!`; the parts being bounded by
`M − R` puts `s` in the range `[R, M−R]`, where the *factorial valley* `s ↦ s!(M−s)!` is at most its
value at `R`, so `C(M,s) ≥ C(M,R)`; and `M^R ≤ 2^R R! C(M,R)` by the descending-factorial bound.

Raised to a positive real power `r` this is exactly the entropy input an endpoint convolution
estimate needs: a product of `d` factorial-envelope terms with no dominant index is smaller than the
single term of index `M` by a factor `M^{-rR}`, uniformly in the composition.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-! ## The factorial valley -/

/-- Moving one step toward the middle does not increase `s!(M−s)!`. -/
theorem factorial_valley_step {M s : ℕ} (h : 2 * s + 1 ≤ M) :
    (s + 1).factorial * (M - (s + 1)).factorial ≤ s.factorial * (M - s).factorial := by
  have hval : M - s = (M - (s + 1)) + 1 := by omega
  have hle : s + 1 ≤ (M - (s + 1)) + 1 := by omega
  rw [hval]
  simp only [Nat.factorial_succ]
  calc (s + 1) * s.factorial * (M - (s + 1)).factorial
      = (s + 1) * (s.factorial * (M - (s + 1)).factorial) := by ring
    _ ≤ ((M - (s + 1)) + 1) * (s.factorial * (M - (s + 1)).factorial) :=
        Nat.mul_le_mul_right _ hle
    _ = s.factorial * (((M - (s + 1)) + 1) * (M - (s + 1)).factorial) := by ring

/-- On the first half the factorial valley is antitone. -/
theorem factorial_valley_antitone {M R s : ℕ} (hRs : R ≤ s) (hs : 2 * s ≤ M) :
    s.factorial * (M - s).factorial ≤ R.factorial * (M - R).factorial := by
  induction s, hRs using Nat.le_induction with
  | base => exact le_rfl
  | succ s hRs ih =>
      have h2s : 2 * s + 1 ≤ M := by omega
      exact le_trans (factorial_valley_step h2s) (ih (by omega))

theorem factorial_valley_symm {M s : ℕ} (h : s ≤ M) :
    s.factorial * (M - s).factorial = (M - s).factorial * (M - (M - s)).factorial := by
  have hval : M - (M - s) = s := by omega
  rw [hval]
  ring

/-- **The factorial valley.**  Between `R` and `M − R` the product `s!(M−s)!` never exceeds its
value at the endpoint `R`. -/
theorem factorial_valley_le {M R s : ℕ} (hRs : R ≤ s) (hsM : s ≤ M - R) :
    s.factorial * (M - s).factorial ≤ R.factorial * (M - R).factorial := by
  by_cases h : 2 * s ≤ M
  · exact factorial_valley_antitone hRs h
  · have hsle : s ≤ M := by omega
    have h1 : R ≤ M - s := by omega
    have h2 : 2 * (M - s) ≤ M := by omega
    rw [factorial_valley_symm hsle]
    exact factorial_valley_antitone h1 h2

/-- **Binomial monotonicity toward the middle.** -/
theorem choose_le_choose_of_between {M R s : ℕ} (hRs : R ≤ s) (hsM : s ≤ M - R)
    (hRM : 2 * R ≤ M) : M.choose R ≤ M.choose s := by
  have hRle : R ≤ M := by omega
  have hsle : s ≤ M := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hRle
  have h2 := Nat.choose_mul_factorial_mul_factorial hsle
  have hval := factorial_valley_le hRs hsM
  have hpos : 0 < R.factorial * (M - R).factorial := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc M.choose R * (R.factorial * (M - R).factorial)
      = M.factorial := by rw [← mul_assoc]; exact h1
    _ = M.choose s * (s.factorial * (M - s).factorial) := by rw [← mul_assoc]; exact h2.symm
    _ ≤ M.choose s * (R.factorial * (M - R).factorial) := Nat.mul_le_mul_left _ hval

/-! ## The multinomial bound -/

/-- The product of the factorials of the parts, times the binomial at the complement of the largest
part, is at most the factorial of the sum. -/
theorem prod_factorial_mul_choose_le {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → ℕ)
    (i₀ : ι) :
    (∏ i, (n i).factorial) * ((∑ i, n i).choose ((∑ i, n i) - n i₀))
      ≤ (∑ i, n i).factorial := by
  classical
  set M : ℕ := ∑ i, n i with hM
  have hmem : i₀ ∈ (Finset.univ : Finset ι) := Finset.mem_univ i₀
  have hmle : n i₀ ≤ M := by
    rw [hM]
    exact Finset.single_le_sum (f := n) (fun i _ => Nat.zero_le _) hmem
  set s : ℕ := M - n i₀ with hs
  have hsum : ∑ i ∈ Finset.univ.erase i₀, n i = s := by
    have := Finset.add_sum_erase (Finset.univ : Finset ι) n hmem
    omega
  have hdvd : (∏ i ∈ Finset.univ.erase i₀, (n i).factorial) ∣ s.factorial := by
    rw [← hsum]
    exact Nat.prod_factorial_dvd_factorial_sum _ _
  have hple : (∏ i ∈ Finset.univ.erase i₀, (n i).factorial) ≤ s.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) hdvd
  have hsplit : ∏ i, (n i).factorial
      = (n i₀).factorial * ∏ i ∈ Finset.univ.erase i₀, (n i).factorial :=
    (Finset.mul_prod_erase (Finset.univ : Finset ι) (fun i => (n i).factorial) hmem).symm
  have hsle : s ≤ M := by omega
  have hchoose := Nat.choose_mul_factorial_mul_factorial hsle
  have hcomp : M - s = n i₀ := by omega
  rw [hcomp] at hchoose
  calc (∏ i, (n i).factorial) * (M.choose s)
      = ((n i₀).factorial * ∏ i ∈ Finset.univ.erase i₀, (n i).factorial) * M.choose s := by
        rw [hsplit]
    _ ≤ ((n i₀).factorial * s.factorial) * M.choose s := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hple)
    _ = M.choose s * s.factorial * (n i₀).factorial := by ring
    _ = M.factorial := hchoose

/-! ## The descending-factorial lower bound -/

/-- **A binomial coefficient is at least `M^R / (2^R R!)`.** -/
theorem pow_le_two_pow_mul_factorial_mul_choose {M R : ℕ} (hRM : 2 * R ≤ M) :
    M ^ R ≤ 2 ^ R * (R.factorial * M.choose R) := by
  have hdesc : M.descFactorial R = R.factorial * M.choose R :=
    Nat.descFactorial_eq_factorial_mul_choose M R
  have hpow : (M + 1 - R) ^ R ≤ M.descFactorial R := Nat.pow_sub_le_descFactorial M R
  have hstep : M ≤ 2 * (M + 1 - R) := by omega
  calc M ^ R ≤ (2 * (M + 1 - R)) ^ R := Nat.pow_le_pow_left hstep R
    _ = 2 ^ R * (M + 1 - R) ^ R := by rw [mul_pow]
    _ ≤ 2 ^ R * M.descFactorial R := Nat.mul_le_mul_left _ hpow
    _ = 2 ^ R * (R.factorial * M.choose R) := by rw [hdesc]

/-! ## The composition bound -/

/-- **The factorial entropy bound.**  A composition of `M` into `d` parts, none of which exceeds
`M − R`, loses the factor `M^R / (2^R R!)` against `M!`. -/
theorem prod_factorial_mul_pow_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (n : ι → ℕ) (R : ℕ) (hpart : ∀ i, n i ≤ (∑ i, n i) - R)
    (hcard : Fintype.card ι * R ≤ ∑ i, n i) (hRM : 2 * R ≤ ∑ i, n i) :
    (∏ i, (n i).factorial) * (∑ i, n i) ^ R ≤ 2 ^ R * (R.factorial * (∑ i, n i).factorial) := by
  classical
  set M : ℕ := ∑ i, n i with hM
  obtain ⟨i₀, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) n ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have hmax' : ∀ i, n i ≤ n i₀ := fun i => hmax i (Finset.mem_univ i)
  -- the largest part is at least the average
  have havg : M ≤ Fintype.card ι * n i₀ := by
    have hle : ∑ i, n i ≤ ∑ _i : ι, n i₀ := Finset.sum_le_sum fun i _ => hmax' i
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    exact hle
  have hcardpos : 0 < Fintype.card ι := Fintype.card_pos
  have hRmax : R ≤ n i₀ := by
    refine Nat.le_of_mul_le_mul_left ?_ hcardpos
    omega
  set s : ℕ := M - n i₀ with hs
  have hmle : n i₀ ≤ M := by
    rw [hM]
    exact Finset.single_le_sum (f := n) (fun i _ => Nat.zero_le _) (Finset.mem_univ i₀)
  have hRs : R ≤ s := by
    have := hpart i₀
    omega
  have hsM : s ≤ M - R := by omega
  have hmono : M.choose R ≤ M.choose s := choose_le_choose_of_between hRs hsM hRM
  have hmain : (∏ i, (n i).factorial) * M.choose R ≤ M.factorial := by
    refine le_trans ?_ (prod_factorial_mul_choose_le n i₀)
    exact Nat.mul_le_mul_left _ hmono
  have hbin := pow_le_two_pow_mul_factorial_mul_choose (M := M) (R := R) hRM
  calc (∏ i, (n i).factorial) * M ^ R
      ≤ (∏ i, (n i).factorial) * (2 ^ R * (R.factorial * M.choose R)) :=
        Nat.mul_le_mul_left _ hbin
    _ = 2 ^ R * R.factorial * ((∏ i, (n i).factorial) * M.choose R) := by ring
    _ ≤ 2 ^ R * R.factorial * M.factorial := Nat.mul_le_mul_left _ hmain
    _ = 2 ^ R * (R.factorial * M.factorial) := by ring

/-- **The factorial entropy bound, real `r`-th power form.** -/
theorem prod_rpow_factorial_mul_pow_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {r : ℝ} (hr : 0 ≤ r) (n : ι → ℕ) (R : ℕ) (hpart : ∀ i, n i ≤ (∑ i, n i) - R)
    (hcard : Fintype.card ι * R ≤ ∑ i, n i) (hRM : 2 * R ≤ ∑ i, n i) :
    (∏ i, (((n i).factorial : ℕ) : ℝ) ^ r) * ((((∑ i, n i) ^ R : ℕ) : ℝ)) ^ r
      ≤ (((2 ^ R * R.factorial : ℕ) : ℝ)) ^ r * ((((∑ i, n i).factorial : ℕ) : ℝ)) ^ r := by
  classical
  have hnat := prod_factorial_mul_pow_le n R hpart hcard hRM
  have hcast : (((∏ i, (n i).factorial) * (∑ i, n i) ^ R : ℕ) : ℝ)
      ≤ (((2 ^ R * (R.factorial * (∑ i, n i).factorial) : ℕ)) : ℝ) := by
    exact_mod_cast hnat
  have hstep : ((((∏ i, (n i).factorial) * (∑ i, n i) ^ R : ℕ) : ℝ)) ^ r
      ≤ ((((2 ^ R * (R.factorial * (∑ i, n i).factorial) : ℕ)) : ℝ)) ^ r :=
    Real.rpow_le_rpow (by positivity) hcast hr
  have hcastprod : (((∏ i, (n i).factorial : ℕ)) : ℝ) = ∏ i, (((n i).factorial : ℕ) : ℝ) := by
    push_cast
    rfl
  have hL : ((((∏ i, (n i).factorial) * (∑ i, n i) ^ R : ℕ) : ℝ)) ^ r
      = (∏ i, (((n i).factorial : ℕ) : ℝ) ^ r) * ((((∑ i, n i) ^ R : ℕ) : ℝ)) ^ r := by
    rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity), hcastprod,
      Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
  have hRid : ((2 ^ R * (R.factorial * (∑ i, n i).factorial) : ℕ))
      = (2 ^ R * R.factorial : ℕ) * ((∑ i, n i).factorial : ℕ) := by ring
  have hR : ((((2 ^ R * (R.factorial * (∑ i, n i).factorial) : ℕ)) : ℝ)) ^ r
      = (((2 ^ R * R.factorial : ℕ) : ℝ)) ^ r * ((((∑ i, n i).factorial : ℕ) : ℝ)) ^ r := by
    rw [hRid, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  rw [← hL, ← hR]
  exact hstep

/-! ## The truncated-product saving -/

/-- **The saving inequality for a truncated factor.**  If a factor of a product contributes at most
`K` to the degree, the binomial saving at the total degree is at most the product of the saving
already present in the complementary factor and the split binomial.  This is the induction step of a
truncated-product estimate, and it needs no hypothesis relating `n` to `K`. -/
theorem choose_sub_le_mul_choose {n q K : ℕ} (hq : q ≤ n) (hqK : q ≤ K) :
    n.choose (n - K) ≤ n.choose q * (n - q).choose ((n - q) - K) := by
  classical
  by_cases hnK : n ≤ K
  · have h0 : n - K = 0 := by omega
    rw [h0, Nat.choose_zero_right]
    have h1 : 0 < n.choose q := Nat.choose_pos hq
    have h2 : 0 < (n - q).choose ((n - q) - K) := Nat.choose_pos (by omega)
    calc 1 ≤ n.choose q := h1
      _ ≤ n.choose q * ((n - q).choose ((n - q) - K)) := Nat.le_mul_of_pos_right _ h2
  · by_cases hpK : n - q ≤ K
    · have h0 : (n - q) - K = 0 := by omega
      rw [h0, Nat.choose_zero_right, mul_one]
      exact choose_le_choose_of_between (by omega) (by omega) (by omega)
    · have hKp : K ≤ n - q := by omega
      have e1 : n.choose (n - K) * (n - K).factorial * K.factorial = n.factorial := by
        have h := Nat.choose_mul_factorial_mul_factorial (show n - K ≤ n by omega)
        have hnK' : n - (n - K) = K := by omega
        rwa [hnK'] at h
      have e2 : n.choose q * q.factorial * (n - q).factorial = n.factorial :=
        Nat.choose_mul_factorial_mul_factorial hq
      have e3 : (n - q).choose ((n - q) - K) * ((n - q) - K).factorial * K.factorial
          = (n - q).factorial := by
        have h := Nat.choose_mul_factorial_mul_factorial (show (n - q) - K ≤ n - q by omega)
        have hpK' : (n - q) - ((n - q) - K) = K := by omega
        rwa [hpK'] at h
      have hdvd : q.factorial * ((n - q) - K).factorial ≤ (n - K).factorial := by
        have hsum : q + ((n - q) - K) = n - K := by omega
        have hd := Nat.factorial_mul_factorial_dvd_factorial_add q ((n - q) - K)
        rw [hsum] at hd
        exact Nat.le_of_dvd (Nat.factorial_pos _) hd
      have hpos : 0 < q.factorial * ((n - q) - K).factorial * K.factorial := by positivity
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      calc n.choose (n - K) * (q.factorial * ((n - q) - K).factorial * K.factorial)
          ≤ n.choose (n - K) * ((n - K).factorial * K.factorial) := by
            refine Nat.mul_le_mul_left _ ?_
            exact Nat.mul_le_mul_right _ hdvd
        _ = n.factorial := by rw [← mul_assoc]; exact e1
        _ = n.choose q * q.factorial * (n - q).factorial := e2.symm
        _ = n.choose q * q.factorial
              * ((n - q).choose ((n - q) - K) * ((n - q) - K).factorial * K.factorial) := by
            rw [e3]
        _ = n.choose q * ((n - q).choose ((n - q) - K))
              * (q.factorial * ((n - q) - K).factorial * K.factorial) := by ring

end GaloisForLFunctions.HTGeometry
