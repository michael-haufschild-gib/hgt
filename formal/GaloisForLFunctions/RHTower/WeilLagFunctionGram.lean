import GaloisForLFunctions.RHTower.WeilLagFunctionRecurrence

/-!
# The lag kernel on the multiplicative group

`K(x, y) = Φ(log x − log y)` is a kernel on the multiplicative group of positive reals, and on the
positive rationals — the group of principal divisors of `Spec ℤ` — its entries are explicit prime
sums: `K(n, m) = Φ(log(n/m))` with `Φ` given by the genus-kernel explicit formula at `X = n/m`.

RH is equivalent to positive semidefiniteness of this kernel: under RH `Φ` is the cosine series
`Σ_ρ w_ρ cos(γ_ρ L)` with positive weights, so every quadratic form is `Σ_ρ w_ρ |Σ_x c_x x^{iγ_ρ}|²`;
conversely the `2×2` minors on `{1, n}` are exactly the integer lag inequalities `a_n ≤ a_1`.
This is the interface any geometric producer of positivity must fill: an intersection pairing on
the divisors of `Spec ℤ` whose regularised values are `Φ(log(n/m))` and whose Hodge-index inequality
is `Φ(0) ≥ Φ(L)`.
-/

open Real Filter Topology

namespace RHTower

noncomputable section

/-- The lag kernel `K(x, y) = Φ(log x − log y)`. -/
def lagGramKernel (x y : ℝ) : ℝ := weilLagFunctionReal (Real.log x - Real.log y)

theorem lagGramKernel_symm (x y : ℝ) : lagGramKernel x y = lagGramKernel y x := by
  unfold lagGramKernel
  rw [← weilLagFunctionReal_neg, neg_sub]

theorem lagGramKernel_self (x : ℝ) : lagGramKernel x x = poleSharpConstant := by
  unfold lagGramKernel
  rw [sub_self]
  have := integerLag_one
  unfold integerLag at this
  rwa [Nat.cast_one, Real.log_one] at this

/-- The quadratic form of the lag kernel on a finite set of points. -/
def lagGramForm (S : Finset ℝ) (c : ℝ → ℝ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, c x * c y * lagGramKernel x y

/-- Under RH the quadratic form is `Σ_ρ w_ρ ((Σ c_x cos(γ log x))² + (Σ c_x sin(γ log x))²)`. -/
theorem lagGramForm_eq_of_riemannHypothesis (h : RiemannHypothesis) (S : Finset ℝ)
    (c : ℝ → ℝ) :
    lagGramForm S c = ∑' q : XiZeroCopy, cosWeight q *
      ((∑ x ∈ S, c x * Real.cos (zeroOrdinate q * Real.log x)) ^ (2 : ℕ) +
        (∑ x ∈ S, c x * Real.sin (zeroOrdinate q * Real.log x)) ^ (2 : ℕ)) := by
  classical
  unfold lagGramForm lagGramKernel
  have hw := summable_cosWeight h
  -- termwise summability
  have hterm : ∀ x y : ℝ, Summable fun q : XiZeroCopy =>
      c x * c y * (cosWeight q * Real.cos (zeroOrdinate q * (Real.log x - Real.log y))) := by
    intro x y
    refine (hw.mul_left (|c x * c y|)).of_norm_bounded fun q => ?_
    calc ‖c x * c y * (cosWeight q * Real.cos (zeroOrdinate q * (Real.log x - Real.log y)))‖
        = |c x * c y| * (cosWeight q * |Real.cos (zeroOrdinate q * (Real.log x - Real.log y))|) := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul (cosWeight q), abs_of_pos (cosWeight_pos q)]
      _ ≤ |c x * c y| * (cosWeight q * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (cosWeight_pos q).le) (abs_nonneg _)
      _ = |c x * c y| * cosWeight q := by ring
  -- rewrite each entry as a tsum and interchange
  have h1 : ∀ x y : ℝ, c x * c y * weilLagFunctionReal (Real.log x - Real.log y)
      = ∑' q : XiZeroCopy, c x * c y *
          (cosWeight q * Real.cos (zeroOrdinate q * (Real.log x - Real.log y))) := by
    intro x y
    rw [weilLagFunctionReal_eq_cos_series h, ← tsum_mul_left]
  simp_rw [h1]
  have h2 : ∀ x ∈ S, (∑ y ∈ S, ∑' q : XiZeroCopy, c x * c y *
      (cosWeight q * Real.cos (zeroOrdinate q * (Real.log x - Real.log y))))
      = ∑' q : XiZeroCopy, ∑ y ∈ S, c x * c y *
          (cosWeight q * Real.cos (zeroOrdinate q * (Real.log x - Real.log y))) := fun x _ =>
    (Summable.tsum_finsetSum fun y _ => hterm x y).symm
  rw [Finset.sum_congr rfl h2]
  rw [← Summable.tsum_finsetSum fun x _ => summable_sum fun y _ => hterm x y]
  congr 1
  funext q
  -- the finite algebra: Σ_{x,y} c_x c_y w cos(γ(a_x − a_y)) = w [(Σ c cos)² + (Σ c sin)²]
  have hcos : ∀ x y : ℝ, Real.cos (zeroOrdinate q * (Real.log x - Real.log y))
      = Real.cos (zeroOrdinate q * Real.log x) * Real.cos (zeroOrdinate q * Real.log y)
        + Real.sin (zeroOrdinate q * Real.log x) * Real.sin (zeroOrdinate q * Real.log y) := by
    intro x y
    rw [mul_sub, Real.cos_sub]
  simp_rw [hcos]
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- Under RH the lag kernel is positive semidefinite. -/
theorem lagGramForm_nonneg_of_riemannHypothesis (h : RiemannHypothesis) (S : Finset ℝ)
    (c : ℝ → ℝ) : 0 ≤ lagGramForm S c := by
  rw [lagGramForm_eq_of_riemannHypothesis h]
  exact tsum_nonneg fun q => mul_nonneg (cosWeight_pos q).le (by positivity)

/-- The quadratic form only sees the support of `c`. -/
theorem lagGramForm_subset {S T : Finset ℝ} (hTS : T ⊆ S) {c : ℝ → ℝ}
    (hc : ∀ x ∈ S, x ∉ T → c x = 0) : lagGramForm S c = lagGramForm T c := by
  unfold lagGramForm
  rw [← Finset.sum_subset hTS (fun x hx hx' => by rw [hc x hx hx']; simp)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_subset hTS (fun y hy hy' => by rw [hc y hy hy']; simp)]

/-- The `2×2` minor on `{1, n}` with weights `1, −1` is `2(a_1 − a_n)`. -/
theorem lagGramForm_pair {n : ℕ} (hn : 2 ≤ n) {c : ℝ → ℝ} (hc1 : c 1 = 1) (hcn : c n = -1) :
    lagGramForm {(1 : ℝ), (n : ℝ)} c = 2 * (poleSharpConstant - integerLag n) := by
  classical
  have hne : (1 : ℝ) ≠ (n : ℝ) := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold lagGramForm
  rw [Finset.sum_pair hne, Finset.sum_pair hne, Finset.sum_pair hne, hc1, hcn]
  rw [lagGramKernel_self, lagGramKernel_self, lagGramKernel_symm (n : ℝ) 1]
  unfold lagGramKernel integerLag
  rw [Real.log_one, zero_sub, weilLagFunctionReal_neg]
  ring

/-- **RH ⟺ the lag kernel is positive semidefinite on the positive reals.** -/
theorem riemannHypothesis_iff_lagGramKernel_posSemidef :
    RiemannHypothesis ↔ ∀ (S : Finset ℝ) (c : ℝ → ℝ), 0 ≤ lagGramForm S c := by
  classical
  refine ⟨fun h S c => lagGramForm_nonneg_of_riemannHypothesis h S c, fun h => ?_⟩
  rw [riemannHypothesis_iff_integerLag_le_sharp]
  intro n hn
  have := h {(1 : ℝ), (n : ℝ)} (fun x => if x = 1 then 1 else -1)
  have hne : (1 : ℝ) ≠ (n : ℝ) := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [lagGramForm_pair hn (by simp) (by simp [hne.symm])] at this
  linarith

/-- The arithmetic Gram form: the kernel on the integers `1, …, N`, i.e. on the divisor group
of `Spec ℤ` generated by the primes up to `N`. -/
def arithmeticGramForm (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, c n * c m * lagGramKernel n m

theorem arithmeticGramForm_eq (N : ℕ) (c : ℕ → ℝ) :
    arithmeticGramForm N c
      = lagGramForm ((Finset.Icc 1 N).image (fun n : ℕ => (n : ℝ))) (fun x => c ⌊x⌋₊) := by
  classical
  have hinj : Set.InjOn (fun n : ℕ => (n : ℝ)) (Finset.Icc 1 N : Set ℕ) := fun a _ b _ hab =>
    Nat.cast_injective hab
  unfold arithmeticGramForm lagGramForm
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [Nat.floor_natCast]

/-- **RH ⟺ every arithmetic Gram matrix `(Φ(log(n/m)))_{n,m ≤ N}` is positive semidefinite.** -/
theorem riemannHypothesis_iff_arithmeticGramForm_nonneg :
    RiemannHypothesis ↔ ∀ (N : ℕ) (c : ℕ → ℝ), 0 ≤ arithmeticGramForm N c := by
  classical
  constructor
  · intro h N c
    rw [arithmeticGramForm_eq]
    exact lagGramForm_nonneg_of_riemannHypothesis h _ _
  · intro h
    rw [riemannHypothesis_iff_integerLag_le_sharp]
    intro n hn
    have hne : (1 : ℝ) ≠ (n : ℝ) := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    set c₀ : ℕ → ℝ := fun k => if k = 1 then 1 else if k = n then -1 else 0 with hc₀
    have hpair := h n c₀
    rw [arithmeticGramForm_eq] at hpair
    have hsub : ({(1 : ℝ), (n : ℝ)} : Finset ℝ) ⊆ (Finset.Icc 1 n).image (fun k : ℕ => (k : ℝ)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_image.mpr ⟨1, by rw [Finset.mem_Icc]; omega, by simp⟩
      · exact Finset.mem_image.mpr ⟨n, by rw [Finset.mem_Icc]; omega, rfl⟩
    have hvan : ∀ x ∈ (Finset.Icc 1 n).image (fun k : ℕ => (k : ℝ)),
        x ∉ ({(1 : ℝ), (n : ℝ)} : Finset ℝ) → (fun x => c₀ ⌊x⌋₊) x = 0 := by
      intro x hx hx'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
      have hk1 : k ≠ 1 := fun h => hx'.1 (by rw [h]; simp)
      have hkn : k ≠ n := fun h => hx'.2 (by rw [h])
      simp [hc₀, Nat.floor_natCast, hk1, hkn]
    rw [lagGramForm_subset hsub hvan] at hpair
    rw [lagGramForm_pair hn (by simp [hc₀]) (by
      simp only [hc₀, Nat.floor_natCast]
      have : n ≠ 1 := by omega
      simp [this])] at hpair
    linarith

end

end RHTower
