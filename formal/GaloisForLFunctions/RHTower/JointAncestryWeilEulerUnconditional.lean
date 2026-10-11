import GaloisForLFunctions.RHTower.JointAncestryWeilEulerBridge
import GaloisForLFunctions.RHTower.JointAncestryLargePrimeMaximalExclusion

/-!
# Unconditional Weil positivity on Euler vectors

Through the Weil–Euler bridge, the unconditional JAS positivity results become unconditional
positivity statements for Weil's lag form `Σ_{m,n} c_m c̄_n Φ(log n − log m)` on explicit families of
*Euler vectors* `c_m = e_w(m) m^{−σ}` (`e_w(m) = Π_{p ∈ P} w_p^{v_p(m)}`, `w ∈ T^P`, `m` running over
the `P`-smooth integers):

* exponent `σ = 2`, every finite prime set (`weilEulerForm_two_nonneg`);
* exponent `σ = 3/2 + ε`, every finite set of primes `p > X(ε)`
  (`exists_weilEulerForm_three_halves_add_nonneg`);
* exponent `σ = 1 + α + ε` on primes `p > X(ε)` under a half-plane bound `α`
  (`weilEulerForm_nonneg_of_xiZeroHalfPlaneBound`).

By the large-prime abscissa law the last statement is sharp off RH: Weil positivity on large-prime
Euler vectors at exponent `σ ∈ (1, 3/2)` is the zero-free half-plane `Re s > σ − ½`.
-/

open Complex

namespace RHTower

noncomputable section

theorem support_jasVecChar_subset (P : Finset Nat.Primes) (x : ↥P → ℕ) :
    (jasVecChar P x).support ⊆ P := by
  classical
  unfold jasVecChar
  refine Finsupp.support_finsetSum.trans fun p hp => ?_
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  have := Finsupp.support_single_subset hi
  rw [Finset.mem_singleton] at this
  rw [this]
  exact i.2

/-- Positivity on a prime set gives nonnegative densities on every sub-torus. -/
theorem re_jasZeroSumDensity_nonneg_of_on {c : ℝ} (hc : 0 < c) {S : Finset Nat.Primes}
    (h : JasDressedPSDOn S (1 / 2 + c)) (P : Finset Nat.Primes) (hP : P ⊆ S) (w : ↥P → ℂ)
    (hw : ∀ i, ‖w i‖ = 1) : 0 ≤ (jasZeroSumDensity c P w).re :=
  re_tsum_prod_jasHoloLocal_nonneg_of_fejer hc P w hw fun K =>
    h _ (jasFejerBox P K) (jasFejerCoeff P w) (jasVecChar P) (jasVecChar_injective P).injOn
      fun x _ => (support_jasVecChar_subset P x).trans hP

/-- Positivity on a prime set gives Weil positivity on its Euler vectors. -/
theorem weilEulerForm_nonneg_of_on {σ : ℝ} (hσ : 1 / 2 < σ) {S : Finset Nat.Primes}
    (h : JasDressedPSDOn S σ) (P : Finset Nat.Primes) (hP : P ⊆ S) (w : ↥P → ℂ)
    (hw : ∀ i, ‖w i‖ = 1) : 0 ≤ (weilEulerForm P w σ).re := by
  obtain ⟨c, rfl⟩ : ∃ c, σ = 1 / 2 + c := ⟨σ - 1 / 2, by ring⟩
  have hc : 0 < c := by linarith
  have hd := re_jasZeroSumDensity_nonneg_of_on hc h P hP w hw
  rw [jasZeroSumDensity_eq_weilEulerForm hc P hw, ← Complex.ofReal_prod,
    Complex.re_ofReal_mul] at hd
  exact nonneg_of_mul_nonneg_right hd (prod_one_sub_exp_pos hc P)

/-- **Weil positivity at exponent `2`.** -/
theorem weilEulerForm_two_nonneg (P : Finset Nat.Primes) (w : ↥P → ℂ) (hw : ∀ i, ‖w i‖ = 1) :
    0 ≤ (weilEulerForm P w 2).re :=
  (jasDressedPSD_iff_weilEulerForm_nonneg (by norm_num)).mp jasDressedPSD_two P w hw

/-- **Weil positivity on large-prime Euler vectors under a half-plane bound.** -/
theorem weilEulerForm_nonneg_of_xiZeroHalfPlaneBound {alpha ε : ℝ} {X : ℕ} (halpha0 : 0 ≤ alpha)
    (hXi : XiZeroHalfPlaneBound alpha) (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 2 ≤ X)
    (hlog : 1 / ε + 1 ≤ Real.log X) (P : Finset Nat.Primes) (hP : ∀ p ∈ P, X < (p : ℕ))
    (w : ↥P → ℂ) (hw : ∀ i, ‖w i‖ = 1) : 0 ≤ (weilEulerForm P w (1 + alpha + ε)).re :=
  weilEulerForm_nonneg_of_on (by linarith)
    (jasDressedPSDAbove_of_xiZeroHalfPlaneBound halpha0 hXi hε hε1 hX hlog P hP) P subset_rfl w hw

/-- **Unconditional Weil positivity at exponent `3/2 + ε` on large-prime Euler vectors.** -/
theorem exists_weilEulerForm_three_halves_add_nonneg {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ X : ℕ, ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) → ∀ w : ↥P → ℂ,
      (∀ i, ‖w i‖ = 1) → 0 ≤ (weilEulerForm P w (3 / 2 + ε)).re := by
  obtain ⟨X, hX⟩ := exists_jasDressedPSDAbove_three_halves_add hε hε1
  exact ⟨X, fun P hP w hw => weilEulerForm_nonneg_of_on (by linarith) (hX P hP) P subset_rfl w hw⟩

end

end RHTower
