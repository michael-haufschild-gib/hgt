import GaloisForLFunctions.RHTower.Matveev.FeldmanAuxiliaryFunction

/-!
# The coefficients of Fel'dman's auxiliary function vanish if its values do

At a natural number `x` the true auxiliary function with `σ = 0`, `τ = 0` is the exponential
polynomial

`Φ_{0,0}(x) = Σ_l Q_l(x) ω_l^x`,  `Q_l = Σ_k C(k, l) g_k`,  `ω_l = ∏_j p_j^{l_j}`.

The bases `ω_l` are distinct positive integers by unique factorization, and every `Q_l` has degree
at most `N`.  So vanishing at `x < (N + 1) q^{m+1}` forces every `Q_l = 0`, and since the `g_k`
are independent, every `C(k, l) = 0`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset Polynomial

variable {m : ℕ} (p : Fin (m + 1) → ℕ) (b : Fin (m + 1) → ℤ)

/-- The base `ω_l = ∏_j p_j^{l_j}` of an exponent vector. -/
def feldmanBase {q : ℕ} (l : Fin (m + 1) → Fin q) : ℕ := ∏ j, p j ^ (l j : ℕ)

/-- The polynomial `Q_l = Σ_k C(k, l) g_k`. -/
def feldmanColumnPoly {N q : ℕ} (C : FeldmanIndex N q m → ℤ) (l : Fin (m + 1) → Fin q) : ℂ[X] :=
  ∑ k : Fin (N + 1), Polynomial.C ((C (k, l) : ℤ) : ℂ) * lagrangeShift N k

theorem feldmanBase_injective (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime) {q : ℕ} :
    Function.Injective (feldmanBase p (q := q)) := by
  intro l l' h
  have hlog := congrArg (fun n : ℕ => Real.log (n : ℝ)) h
  simp only [feldmanBase] at hlog
  rw [log_prod_pow p hprime univ, log_prod_pow p hprime univ] at hlog
  have hzero : primeLogForm p (fun j => ((l j : ℕ) : ℤ) - ((l' j : ℕ) : ℤ)) = 0 := by
    unfold primeLogForm
    push_cast
    simp only [sub_mul, sum_sub_distrib]
    linarith
  have hvec := (primeLogForm_eq_zero_iff p hp hprime _).mp hzero
  funext j
  have := congrFun hvec j
  simp only [Pi.zero_apply, sub_eq_zero] at this
  exact Fin.ext (by exact_mod_cast this)

theorem feldmanBase_pos (hprime : ∀ i, (p i).Prime) {q : ℕ} (l : Fin (m + 1) → Fin q) :
    0 < feldmanBase p l :=
  prod_pos fun j _ => pow_pos (hprime j).pos _

theorem natDegree_feldmanColumnPoly_le {N q : ℕ} (C : FeldmanIndex N q m → ℤ)
    (l : Fin (m + 1) → Fin q) : (feldmanColumnPoly C l).natDegree ≤ N := by
  unfold feldmanColumnPoly
  refine (natDegree_sum_le _ _).trans (Finset.sup_le fun k _ => ?_)
  exact (natDegree_C_mul_le _ _).trans
    (natDegree_lagrangeShift_le (Nat.lt_succ_iff.mp k.isLt))

/-- **The value at a natural number as an exponential polynomial.** -/
theorem feldmanTrueAux_zero_natCast (hprime : ∀ i, (p i).Prime) {N q : ℕ}
    (C : FeldmanIndex N q m → ℤ) (x : ℕ) :
    feldmanTrueAux p b N q C 0 0 (x : ℂ) =
      ∑ l : Fin (m + 1) → Fin q,
        (feldmanColumnPoly C l).eval (x : ℂ) * ((feldmanBase p l : ℕ) : ℂ) ^ x := by
  have hp0 : ∀ j, 0 < p j := fun j => (hprime j).pos
  unfold feldmanTrueAux
  rw [Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun l _ => ?_
  unfold feldmanColumnPoly
  rw [eval_finsetSum, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  have hw : gammaWeight b (FeldmanIndex.expo (k, l)) 0 = 1 := by
    simp [gammaWeight]
  have hjet : feldmanJet N k 0 (x : ℂ) = (lagrangeShift (K := ℂ) N k).eval (x : ℂ) := by
    simp [feldmanJet, hasseDeriv_zero, lagrangeShift, feldmanPoly]
  have hexp : Complex.exp ((x : ℂ) * (trueFreq p (FeldmanIndex.expo (k, l)) : ℂ)) =
      ((feldmanBase p l : ℕ) : ℂ) ^ x := by
    rw [exp_natCast_mul_trueFreq p hp0, feldmanBase]
    push_cast
    rw [← prod_pow]
    refine prod_congr rfl fun j _ => ?_
    rw [← pow_mul]
    rfl
  rw [hw, hjet, hexp, eval_mul, eval_C]
  ring

/-- **Vanishing values force vanishing coefficients.** -/
theorem eq_zero_of_feldmanTrueAux_eq_zero (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    {N q : ℕ} (C : FeldmanIndex N q m → ℤ)
    (h : ∀ x : ℕ, x < (N + 1) * q ^ (m + 1) → feldmanTrueAux p b N q C 0 0 (x : ℂ) = 0) :
    C = 0 := by
  classical
  have hQ := eq_zero_of_expPoly_eval_eq_zero (K := ℂ) (univ : Finset (Fin (m + 1) → Fin q))
    (fun l => ((feldmanBase p l : ℕ) : ℂ))
    (fun l _ l' _ hll' => feldmanBase_injective p hp hprime (by exact_mod_cast hll'))
    (fun l _ => by exact_mod_cast (feldmanBase_pos p hprime l).ne')
    N (feldmanColumnPoly C) (fun l _ => natDegree_feldmanColumnPoly_le C l)
    (fun x hx => by
      rw [← feldmanTrueAux_zero_natCast p b hprime C x]
      refine h x ?_
      simpa [Fintype.card_pi, Fintype.card_fin] using hx)
  funext kl
  obtain ⟨k, l⟩ := kl
  have hl := hQ l (mem_univ l)
  have hsum : ∑ i ∈ range (N + 1), Polynomial.C
      ((fun i => if hi : i < N + 1 then ((C (⟨i, hi⟩, l) : ℤ) : ℂ) else 0) i) *
        lagrangeShift (K := ℂ) N i = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => Polynomial.C
      ((fun i => if hi : i < N + 1 then ((C (⟨i, hi⟩, l) : ℤ) : ℂ) else 0) i) *
        lagrangeShift (K := ℂ) N i)]
    simp only [Fin.is_lt, dif_pos, Fin.eta]
    exact hl
  have hk := eq_zero_of_sum_lagrangeShift_eq_zero _ hsum k (mem_range.mpr k.isLt)
  simp only [k.isLt, dif_pos, Fin.eta, Int.cast_eq_zero] at hk
  exact hk

end GaloisForLFunctions.RHTower.Matveev
