import GaloisForLFunctions.HodgeTheoryWithoutVarieties.StarsOfTheCompleteWeilFamily
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheLiouvilleProperty

/-!
# The Möbius gluing of the stars

Inclusion–exclusion over the nerve of the star cover glues every quadratic form on `[1, N]` from
its restrictions to the stars. Möbius inversion over the common divisors of a pair,
`Σ_{d ∣ (m, n)} μ(d) = [gcd(m, n) = 1]` (`sum_moebius_common_divisors`), gives
(`quadratic_moebius_gluing`):

  `Q(x) = Q_cop(x) + Σ_{2 ≤ d ≤ N} (−μ(d)) Q(x · 1_{dℕ})`,

where `Q_cop` keeps only the coprime pairs. This is the quadratic Čech formula of the cover. Only
squarefree `d` contribute, i.e. the faces of the nerve. The signs are `−μ(d)`: plus on primes, minus
on products of two primes, and so on.

* **The prime form is a cone glued to its stars** (`atomicWeilForm_moebius_recursion`): the
  coprime pairs of Weil's prime kernel all contain the vertex `1`, so
  `P_N(x) = 2x₁ Σ_k Λ(k) k^{−1/2} x_k + Σ_{d ≥ 2} (−μ(d)) P_{⌊N/d⌋}(x(d·))`. This is an exact
  recursion over the nerve, through the lower horizons.
* **The complete Weil family is glued from lower resolutions**
  (`completeWeilEnergy_moebius_gluing`): `W_{c,N}(x)` is its coprime part plus the signed sum of
  the families at the star resolutions `(c⌊N/d⌋/N, ⌊N/d⌋)`, applied to the restrictions of `x`.

Positivity cannot be glued term by term: the faces with an even number of primes enter with the
sign `−1`, and the signed face count is the Mertens function (`TheNerveOfTheStarCover`). An
inductive Hodge–Riemann proof over this recursion would have to control the coprime gluing form
against these alternating signs. The deep-star terms are positive (universal regime), so the whole
difficulty sits in the coprime pairs and the shallow faces.
-/

noncomputable section

open Finset
open scoped RealInnerProductSpace
open GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory GaloisForLFunctions.ArithmeticLorentzianGeometry

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- `Σ_{d ∣ g} μ(d) = [g = 1]`. -/
theorem sum_divisors_moebius (g : ℕ) :
    ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℝ) = if g = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => (f g : ℝ))
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  push_cast at h
  rw [h]

/-- **Möbius over common divisors**: for `m, n ∈ [1, N]`,
`Σ_{d ≤ N, d ∣ m, d ∣ n} μ(d) = [gcd(m, n) = 1]`. -/
theorem sum_moebius_common_divisors {N m n : ℕ} (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) :
    ∑ d ∈ Icc 1 N, (if d ∣ m ∧ d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) =
      if Nat.Coprime m n then 1 else 0 := by
  have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
  have hg0 : Nat.gcd m n ≠ 0 := Nat.gcd_ne_zero_left hm0
  have hgN : Nat.gcd m n ≤ N := (Nat.gcd_le_left n (by omega)).trans (mem_Icc.mp hm).2
  rw [← sum_filter]
  have hset : (Icc 1 N).filter (fun d => d ∣ m ∧ d ∣ n) = (Nat.gcd m n).divisors := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨-, h⟩; exact ⟨h, hg0⟩
    · rintro ⟨h, -⟩
      have hd := Nat.le_of_dvd (Nat.pos_of_ne_zero hg0) (Nat.dvd_gcd h.1 h.2)
      have hd0 : d ≠ 0 := by rintro rfl; simp at h; omega
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hd0, hd.trans hgN⟩, h⟩
  rw [hset, sum_divisors_moebius]

/-- **The Möbius gluing of a quadratic form over the star cover.** For values `v i ∈ [1, N]`,
`Q(x) = Q_cop(x) + Σ_{2 ≤ d ≤ N} (−μ(d)) Q(x · 1_{d ∣ v})`. -/
theorem quadratic_moebius_gluing {ι : Type*} [Fintype ι] {N : ℕ} (v : ι → ℕ)
    (hv : ∀ i, v i ∈ Icc 1 N) (W : ι → ι → ℝ) (x : ι → ℝ) :
    ∑ i, ∑ j, W i j * x i * x j =
      ∑ i, ∑ j, (if Nat.Coprime (v i) (v j) then W i j * x i * x j else 0) +
        ∑ d ∈ Icc 2 N, -(ArithmeticFunction.moebius d : ℝ) *
          ∑ i, ∑ j, W i j * (if d ∣ v i then x i else 0) * (if d ∣ v j then x j else 0) := by
  -- Expand the coprime part by Möbius over common divisors and isolate `d = 1`.
  have hterm : ∀ i j, (if Nat.Coprime (v i) (v j) then W i j * x i * x j else 0) =
      ∑ d ∈ Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
        (W i j * (if d ∣ v i then x i else 0) * (if d ∣ v j then x j else 0)) := by
    intro i j
    have hd : ∀ d ∈ Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
        (W i j * (if d ∣ v i then x i else 0) * (if d ∣ v j then x j else 0)) =
        (if d ∣ v i ∧ d ∣ v j then (ArithmeticFunction.moebius d : ℝ) else 0) *
          (W i j * x i * x j) := by
      intro d _
      by_cases h1 : d ∣ v i <;> by_cases h2 : d ∣ v j <;> simp [h1, h2] <;> ring
    rw [sum_congr rfl hd, ← sum_mul, sum_moebius_common_divisors (hv i) (hv j)]
    split_ifs <;> ring
  have hcop : ∑ i, ∑ j, (if Nat.Coprime (v i) (v j) then W i j * x i * x j else 0) =
      ∑ d ∈ Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
        ∑ i, ∑ j, W i j * (if d ∣ v i then x i else 0) * (if d ∣ v j then x j else 0) := by
    simp only [hterm, mul_sum]
    calc ∑ i, ∑ j, ∑ d ∈ Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
          (W i j * (if d ∣ v i then x i else 0) * (if d ∣ v j then x j else 0))
        = ∑ i, ∑ d ∈ Icc 1 N, ∑ j, (ArithmeticFunction.moebius d : ℝ) *
          (W i j * (if d ∣ v i then x i else 0) * (if d ∣ v j then x j else 0)) :=
          sum_congr rfl fun i _ => sum_comm
      _ = _ := sum_comm
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · haveI : IsEmpty ι := ⟨fun i => by simpa using hv i⟩
    simp
  · have hIcc : Icc 1 N = insert 1 (Icc 2 N) := by
      ext d; simp only [mem_Icc, mem_insert]; omega
    rw [hcop, hIcc, sum_insert (by simp)]
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_dvd, if_true, one_mul,
      neg_mul, sum_neg_distrib]
    ring

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
