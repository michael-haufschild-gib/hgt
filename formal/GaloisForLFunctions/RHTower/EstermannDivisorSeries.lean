import GaloisForLFunctions.RHTower.EstermannZeta

/-!
# Estermann's zeta function as a twisted divisor series

Regrouping the absolutely convergent double series for `D(s, a/q)` by the product of its two
indices turns it into a single Dirichlet series with the divisor function as coefficient:

```text
D(s, a/q) = ∑_{N ≥ 1} d(N) e(aN/q) N^{-s},      Re s > 1.
```

The regrouping step is isolated as `hasSum_divisorCount`, which holds for an arbitrary summand
depending only on the product: the fibre of `(m, n) ↦ mn` over `N` is `N.divisorsAntidiagonal`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The fibre of `(m, n) ↦ (m+1)(n+1)` over `N` is the divisor antidiagonal of `N`. -/
def productFiberEquiv (N : ℕ) :
    {p : ℕ × ℕ // (p.1 + 1) * (p.2 + 1) = N} ≃ ((N.divisorsAntidiagonal : Finset (ℕ × ℕ)) : Type) where
  toFun p := ⟨(p.1.1 + 1, p.1.2 + 1), by
    have hne : N ≠ 0 := by
      rw [← p.2]; exact Nat.mul_ne_zero (Nat.succ_ne_zero _) (Nat.succ_ne_zero _)
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨p.2, hne⟩⟩
  invFun d := ⟨(d.1.1 - 1, d.1.2 - 1), by
    obtain ⟨hd, hne⟩ := Nat.mem_divisorsAntidiagonal.mp d.2
    have h1 : 1 ≤ d.1.1 := Nat.one_le_iff_ne_zero.mpr fun h => hne (by rw [← hd, h, zero_mul])
    have h2 : 1 ≤ d.1.2 := Nat.one_le_iff_ne_zero.mpr fun h => hne (by rw [← hd, h, mul_zero])
    rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
    exact hd⟩
  left_inv p := by ext <;> simp
  right_inv d := by
    obtain ⟨hd, hne⟩ := Nat.mem_divisorsAntidiagonal.mp d.2
    have h1 : 1 ≤ d.1.1 := Nat.one_le_iff_ne_zero.mpr fun h => hne (by rw [← hd, h, zero_mul])
    have h2 : 1 ≤ d.1.2 := Nat.one_le_iff_ne_zero.mpr fun h => hne (by rw [← hd, h, mul_zero])
    ext
    · simpa using Nat.sub_add_cancel h1
    · simpa using Nat.sub_add_cancel h2

/-- **Regrouping a double series by the product of its indices.**  If a summand depending only on
the product `(m+1)(n+1)` is summable over `ℕ × ℕ`, then the same total is obtained by summing the
divisor-counted single series. -/
theorem hasSum_divisorCount {F : ℕ → ℂ} {A : ℂ}
    (h : HasSum (fun p : ℕ × ℕ => F ((p.1 + 1) * (p.2 + 1))) A) :
    HasSum (fun N : ℕ => (N.divisors.card : ℂ) * F N) A := by
  have h' : HasSum (fun x : (Σ N : ℕ, {p : ℕ × ℕ // (p.1 + 1) * (p.2 + 1) = N}) =>
      F ((x.2.1.1 + 1) * (x.2.1.2 + 1))) A :=
    (Equiv.hasSum_iff (Equiv.sigmaFiberEquiv fun p : ℕ × ℕ => (p.1 + 1) * (p.2 + 1))).mpr h
  refine h'.sigma ?_
  intro N
  haveI : Fintype {p : ℕ × ℕ // (p.1 + 1) * (p.2 + 1) = N} :=
    Fintype.ofEquiv _ (productFiberEquiv N).symm
  have hcard : Fintype.card {p : ℕ × ℕ // (p.1 + 1) * (p.2 + 1) = N} = N.divisors.card := by
    rw [Fintype.card_congr (productFiberEquiv N), Fintype.card_coe,
      ← Nat.map_div_right_divisors, Finset.card_map]
  have hcst : ∀ c ∈ (Finset.univ : Finset {p : ℕ × ℕ // (p.1 + 1) * (p.2 + 1) = N}),
      F ((c.1.1 + 1) * (c.1.2 + 1)) = F N := fun c _ => by rw [c.2]
  have hsum : (∑ c : {p : ℕ × ℕ // (p.1 + 1) * (p.2 + 1) = N},
      F ((c.1.1 + 1) * (c.1.2 + 1))) = (N.divisors.card : ℂ) * F N := by
    rw [Finset.sum_congr rfl hcst, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  rw [← hsum]
  exact hasSum_fintype _

/-- **Estermann's zeta function is the twisted divisor series.** -/
theorem hasSum_estermannZeta_divisor {q : ℕ} [NeZero q] (a : ZMod q) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun N : ℕ => (N.divisors.card : ℂ) *
        ((ZMod.stdAddChar (a * (N : ZMod q)) : ℂ) / (N : ℂ) ^ s))
      (estermannZeta q a s) := by
  refine hasSum_divisorCount (F := fun N : ℕ =>
    (ZMod.stdAddChar (a * (N : ZMod q)) : ℂ) / (N : ℂ) ^ s) ?_
  refine (hasSum_estermannZeta a hs).congr_fun ?_
  intro p
  have hchar : ((((p.1 + 1) * (p.2 + 1) : ℕ) : ZMod q)) =
      ((p.1 + 1 : ℕ) : ZMod q) * ((p.2 + 1 : ℕ) : ZMod q) := by push_cast; ring
  have hden : ((((p.1 + 1) * (p.2 + 1) : ℕ) : ℂ)) ^ s
      = (((p.1 + 1 : ℕ) : ℂ)) ^ s * (((p.2 + 1 : ℕ) : ℂ)) ^ s := by
    have h1 : (0 : ℝ) ≤ ((p.1 + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ ((p.2 + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have := Complex.mul_cpow_ofReal_nonneg h1 h2 s
    push_cast at this ⊢
    exact this
  rw [hchar, hden, ← mul_assoc]

/-- The twisted divisor coefficient `d(N) e(aN/q)`. -/
def estermannCoeff (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) : ℂ :=
  (N.divisors.card : ℂ) * (ZMod.stdAddChar (a * (N : ZMod q)) : ℂ)

/-- The Dirichlet series of `estermannCoeff` converges to `D(s, a/q)` right of the line `Re s = 1`. -/
theorem hasSum_term_estermannCoeff {q : ℕ} [NeZero q] (a : ZMod q) {s : ℂ} (hs : 1 < s.re) :
    HasSum (LSeries.term (estermannCoeff q a) s) (estermannZeta q a s) := by
  refine (hasSum_estermannZeta_divisor a hs).congr_fun ?_
  intro N
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · rw [LSeries.term_of_ne_zero hN, estermannCoeff, mul_div_assoc]

theorem LSeriesSummable_estermannCoeff {q : ℕ} [NeZero q] (a : ZMod q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (estermannCoeff q a) s :=
  (hasSum_term_estermannCoeff a hs).summable

/-- **`D(s, a/q) = ∑ d(N) e(aN/q) N^{-s}`.** -/
theorem LSeries_estermannCoeff {q : ℕ} [NeZero q] (a : ZMod q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (estermannCoeff q a) s = estermannZeta q a s :=
  (hasSum_term_estermannCoeff a hs).tsum_eq

end

end RHTower
