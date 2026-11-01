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
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticLorentzianGeometry

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- `Σ_{d ∣ g} μ(d) = [g = 1]`. -/
theorem sum_divisors_moebius (g : ℕ) :
    ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℝ) = if g = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => (f g : ℝ))
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  push_cast at h
  rw [h]

/-- **Möbius over common divisors**: for `m ∈ [1, N]` and every `n`,
`Σ_{d ≤ N, d ∣ m, d ∣ n} μ(d) = [gcd(m, n) = 1]`. -/
theorem sum_moebius_common_divisors {N m : ℕ} (hm : m ∈ Icc 1 N) (n : ℕ) :
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
      by_cases h1 : d ∣ v i <;> by_cases h2 : d ∣ v j <;> simp [h1, h2]
    rw [sum_congr rfl hd, ← sum_mul, sum_moebius_common_divisors (hv i) (v j)]
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


/-! ### The prime form is a cone glued to its stars -/

theorem weilPrimeKernel_one_one : weilPrimeKernel 1 1 = 0 := by
  simp [weilPrimeKernel]

/-- Coprime pairs of Weil's prime kernel contain the vertex `1`. -/
theorem weilPrimeKernel_eq_zero_of_coprime {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h : Nat.Coprime m n) : weilPrimeKernel m n = 0 := by
  unfold weilPrimeKernel
  rw [if_neg, if_neg]
  · rintro ⟨hdvd, -⟩; have := Nat.Coprime.eq_one_of_dvd h.symm hdvd; omega
  · rintro ⟨hdvd, -⟩; have := Nat.Coprime.eq_one_of_dvd h hdvd; omega

/-- On a pair of the horizon the coprime part of Weil's prime kernel is the cone of the vertex `1`.
-/
theorem coprime_weilPrimeKernel_eq {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (x : ℕ → ℝ) :
    (if Nat.Coprime m n then weilPrimeKernel m n * x m * x n else 0) =
      (if m = 1 then weilPrimeKernel 1 n * x 1 * x n else 0) +
        (if n = 1 then weilPrimeKernel 1 m * x 1 * x m else 0) := by
  rcases eq_or_lt_of_le hm with rfl | hm2
  · rcases eq_or_lt_of_le hn with rfl | hn2
    · simp [weilPrimeKernel_one_one]
    · simp [show n ≠ 1 by omega]
  · rcases eq_or_lt_of_le hn with rfl | hn2
    · simp [show m ≠ 1 by omega, weilPrimeKernel_comm m 1]; ring
    · rw [if_neg (by omega : m ≠ 1), if_neg (by omega : n ≠ 1), add_zero]
      split_ifs with h
      · rw [weilPrimeKernel_eq_zero_of_coprime hm2 hn2 h]; ring
      · rfl

/-- **The prime form is a cone glued to its stars.**
`P_N(x) = 2x₁ Σ_{k ≤ N} P(1, k) x_k + Σ_{2 ≤ d ≤ N} (−μ(d)) P_{⌊N/d⌋}(x(d·))`. -/
theorem atomicWeilForm_moebius_recursion (N : ℕ) (x : ℕ → ℝ) :
    atomicWeilForm N x = 2 * x 1 * ∑ k ∈ Icc 1 N, weilPrimeKernel 1 k * x k +
      ∑ d ∈ Icc 2 N, -(ArithmeticFunction.moebius d : ℝ) *
        atomicWeilForm (N / d) (starPullback d x) := by
  have hform : ∀ y : ℕ → ℝ, atomicWeilForm N y =
      ∑ i : Icc 1 N, ∑ j : Icc 1 N, weilPrimeKernel i j * y i * y j := by
    intro y
    rw [atomicWeilForm, ← sum_coe_sort (Icc 1 N)]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_coe_sort (Icc 1 N)]
    exact sum_congr rfl fun j _ => by ring
  have hglue := quadratic_moebius_gluing (N := N) (fun i : Icc 1 N => (i : ℕ)) (fun i => i.2)
    (fun i j => weilPrimeKernel i j) (fun i => x i)
  rw [hform, hglue]
  congr 1
  · -- the coprime part is the cone of the vertex `1`
    have hcone : ∀ i j : Icc 1 N,
        (if Nat.Coprime (i : ℕ) j then weilPrimeKernel i j * x i * x j else 0) =
          (if (i : ℕ) = 1 then weilPrimeKernel 1 j * x 1 * x j else 0) +
            (if (j : ℕ) = 1 then weilPrimeKernel 1 i * x 1 * x i else 0) := fun i j =>
      coprime_weilPrimeKernel_eq (mem_Icc.mp i.2).1 (mem_Icc.mp j.2).1 x
    simp only [hcone, sum_add_distrib]
    rw [sum_comm (s := univ) (t := univ) (f := fun i j : Icc 1 N =>
      if (j : ℕ) = 1 then weilPrimeKernel 1 i * x 1 * x i else 0)]
    have hsum : ∀ g : ℕ → ℝ, ∑ i : Icc 1 N, ∑ j : Icc 1 N,
        (if (i : ℕ) = 1 then g j else 0) = ∑ k ∈ Icc 1 N, g k := by
      intro g
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · have h0 : ∀ i : Icc 1 0, False := fun i => by have := mem_Icc.mp i.2; omega
        rw [sum_eq_zero fun i _ => (h0 i).elim, sum_eq_zero fun k hk => by
          have := mem_Icc.mp hk; omega]
      · rw [sum_eq_single (⟨1, mem_Icc.mpr ⟨le_rfl, hN⟩⟩ : Icc 1 N)]
        · simp only
          exact sum_coe_sort (Icc 1 N) g
        · intro b _ hb
          refine sum_eq_zero fun j _ => if_neg fun h => hb (Subtype.ext h)
        · simp
    rw [hsum (fun k => weilPrimeKernel 1 k * x 1 * x k), mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  · refine sum_congr rfl fun d hd => ?_
    have hd0 : 0 < d := by have := (mem_Icc.mp hd).1; omega
    congr 1
    rw [← atomicWeilForm_starRestrict hd0, hform]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [starRestrict]


/-! ### The complete Weil family is glued from lower resolutions -/

/-- The pullback of a horizon vector to the star of `d`, read at horizon `⌊N/d⌋`. -/
def starPull (d N : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    EuclideanSpace ℝ (PrimeHorizonIndex (N / d)) :=
  WithLp.toLp 2 fun a => primeHorizonExtension x (d * a)

/-- Embedding the pullback back into the star is the restriction to the multiples of `d`. -/
theorem starEmbed_starPull {d N : ℕ} (hd : 0 < d) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    (fun n : PrimeHorizonIndex N => starEmbed d N (starPull d N x) n) =
      fun n : PrimeHorizonIndex N => if d ∣ (n : ℕ) then x n else 0 := by
  funext n
  simp only [starEmbed, starPull]
  split_ifs with h
  · obtain ⟨a, ha⟩ := h
    have hn := mem_Icc.mp n.2
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h0
      · simp at ha; omega
      · exact h0
    have haM : a ≤ N / d := (Nat.le_div_iff_mul_le hd).mpr (by rw [mul_comm, ← ha]; exact hn.2)
    rw [ha, Nat.mul_div_cancel_left a hd]
    simp only [primeHorizonExtension, dif_pos (mem_Icc.mpr ⟨ha1, haM⟩)]
    rw [← ha, dif_pos n.2]
  · rfl

/-- **The Möbius gluing of the complete Weil family.** `W_{c,N}(x)` is its coprime part plus the
signed sum of the families at the star resolutions `(c⌊N/d⌋/N, ⌊N/d⌋)`, `2 ≤ d ≤ N`, applied to the
pullbacks of `x`. -/
theorem completeWeilEnergy_moebius_gluing {φ : ℝ → ℝ} (hφ : EdgeHodgeTheory.Admissible φ) {c : ℝ}
    (hc : 0 < c) (N : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N x =
      ∑ i : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
        (if Nat.Coprime (i : ℕ) j then completeWeilMatrix φ c N i j * x i * x j else 0) +
        ∑ d ∈ Icc 2 N, -(ArithmeticFunction.moebius d : ℝ) *
          completeWeilEnergy φ (starOverlap c N d) (N / d) (starPull d N x) := by
  have hqf : ∀ y : EuclideanSpace ℝ (PrimeHorizonIndex N), completeWeilEnergy φ c N y =
      ∑ i : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
        completeWeilMatrix φ c N i j * y i * y j := by
    intro y
    rw [completeWeilEnergy_eq_qf, qf, bil, dotProduct]
    refine sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [hqf, quadratic_moebius_gluing (N := N) (fun i : PrimeHorizonIndex N => (i : ℕ))
    (fun i => i.2) (completeWeilMatrix φ c N) (fun i => x i)]
  congr 1
  refine sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := by have := (mem_Icc.mp hd).1; omega
  have hdN : d ≤ N := (mem_Icc.mp hd).2
  rw [← completeWeilEnergy_starEmbed hφ.contDiff hφ.supp hc hd0 hdN, hqf]
  have hr : ∀ n : PrimeHorizonIndex N,
      starEmbed d N (starPull d N x) n = if d ∣ (n : ℕ) then x n else 0 :=
    fun n => congrFun (starEmbed_starPull hd0 x) n
  simp only [hr]

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
