import GaloisForLFunctions.SignedArithmeticCorrespondences.ThePrimeDebitOfInterleavingSelfIntersections
import GaloisForLFunctions.SelectiveArithmetic.TheLiouvilleTwistFailsBeyondTheTrivialAperture

/-!
# Divisor incidence on late combs

Decompose the `w`-weighted Weil bilinear form `formBilinW w S c e` into its four
constituent pieces: the pole-plane (endpoint) product `poleTerm`, the diagonal
counterterm `diagTerm`, the archimedean jet pairing `jetTerm`, and the prime-power
contact pairing `contactTerm`.

On a late comb `S = Ioc N (N + 3KN)`, three elementary divisibility counts govern
centered prime-divisibility masks `v_p(n) = 1_{p ∣ n} - 1/p`:

1. **Coprime contact bijection and Liouville shift**: every contact pair in `S` has
   ratio `2 ≤ r ≤ 3K`. When `gcd(d_1, r) = gcd(d_2, r) = 1`, multiplication by `r`
   identifies contact incidences on `S` with diagonal incidences on the slices
   `combSlice N K r = Ioc N ((N + 3KN) / r)`. Replacing `Λ` by
   `SelectiveArithmetic.liouvilleWeight` leaves pole, diagonal, and jet terms
   unchanged and flips only nonsquare contact ratios `2 ≤ r ≤ 3K` from `-Λ(r)` to
   `+Λ(r)`, strictly increasing the self-pairing.
2. **Chinese Remainder shifted-incidence cancellation**: for coprime `d_1, d_2 ≥ 2`
   and any shift `h`, the joint condition `d_1 ∣ m ∧ d_2 ∣ (m + h)` is a single
   congruence class modulo `d_1 d_2`, canceling the bulk density `1 / (d_1 d_2)`
   to leave `|∑_{m ∈ (a, b]} v_{d_1}(m) v_{d_2}(m + h)| ≤ 2`. Grouping the singular
   jet kernel by `h = |m - n|` and summing the smooth pieces by parts bounds the
   mixed bilinear entry `|formBilinW w S v_p v_q| ≤ C_{K, w} (1 + log N)` uniformly
   for all distinct primes `p ≠ q`.
3. **Complete-period variance bound**: partitioning `(a, b]` into `⌊(b - a) / d⌋`
   full periods of length `d` gives `∑_{n ∈ (a, b]} v_d(n)^2 ≥ ⌊(b - a) / d⌋ (1 - 1/d)`.
-/

noncomputable section

namespace GaloisForLFunctions.SignedArithmeticCorrespondences

open Finset Filter Topology
open AbsoluteGeometryOfSpecZ (jetKernel jetKernel_comm)
open HodgeTheoryOfAFixedPart
open scoped ArithmeticFunction.vonMangoldt

/-! ### Four-part bilinear decomposition of the weighted Weil form -/

/-- Endpoint (pole-plane) bilinear form `d_1(c) d_2(e) + d_2(c) d_1(e)`. -/
def poleTerm (S : Finset ℕ) (c e : ℕ → ℝ) : ℝ :=
  degOne S c * degTwo S e + degTwo S c * degOne S e

/-- Diagonal counterterm bilinear form `∑_{n ∈ S} c(n) e(n) log(n / 2π)`. -/
def diagTerm (S : Finset ℕ) (c e : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, c n * e n * counterterm n

/-- Off-diagonal archimedean jet bilinear form. -/
def jetTerm (S : Finset ℕ) (c e : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, ∑ m ∈ S.erase n, c m * e n * jetKernel m n

/-- Off-diagonal `w`-weighted prime-power contact bilinear form. -/
def contactTerm (w : ℕ → ℝ) (S : Finset ℕ) (c e : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, ∑ m ∈ S.erase n, c m * e n * contactW w m n

/-- Symmetric `w`-weighted Weil bilinear form on a finite comb `S`. -/
def formBilinW (w : ℕ → ℝ) (S : Finset ℕ) (c e : ℕ → ℝ) : ℝ :=
  poleTerm S c e + diagTerm S c e - jetTerm S c e - contactTerm w S c e

/-- Ratio-`r` divisor slice `(N, ⌊(N + 3KN) / r⌋]` of the late comb `(N, N + 3KN]`. -/
def combSlice (N K r : ℕ) : Finset ℕ :=
  Ioc N ((N + 3 * K * N) / r)

theorem formBilinW_eq_four_parts (w : ℕ → ℝ) (S : Finset ℕ) (c e : ℕ → ℝ) :
    formBilinW w S c e =
      poleTerm S c e + diagTerm S c e - jetTerm S c e - contactTerm w S c e :=
  rfl

theorem formBilinW_self (w : ℕ → ℝ) (S : Finset ℕ) (c : ℕ → ℝ) :
    formBilinW w S c c = combFormW w S c := by
  have hdiag : diagTerm S c c = ∑ n ∈ S, c n ^ 2 * counterterm n :=
    sum_congr rfl fun n _ => by ring
  have hoff : ∑ n ∈ S, ∑ m ∈ S.erase n, c m * c n * (jetKernel m n + contactW w m n) =
      jetTerm S c c + contactTerm w S c c := by
    simp only [jetTerm, contactTerm, mul_add, sum_add_distrib]
  rw [formBilinW, poleTerm, hdiag, combFormW, combPairingW, hoff]
  ring

theorem formBilinW_vonMangoldt (S : Finset ℕ) (c e : ℕ → ℝ) :
    formBilinW (fun k => (Λ k : ℝ)) S c e = formBilin S c e := by
  have hpair : ∑ n ∈ S, ∑ m ∈ S.erase n, c m * e n * pairKernel m n =
      jetTerm S c e + contactTerm (fun k => (Λ k : ℝ)) S c e := by
    simp only [pairKernel, jetTerm, contactTerm, mul_add, sum_add_distrib]
    rfl
  rw [formBilinW, poleTerm, diagTerm, formBilin, combBilin, hpair]
  ring

private theorem contactW_comm (w : ℕ → ℝ) (m n : ℕ) :
    contactW w m n = contactW w n m :=
  add_comm _ _

theorem formBilinW_comm (w : ℕ → ℝ) (S : Finset ℕ) (c e : ℕ → ℝ) :
    formBilinW w S c e = formBilinW w S e c := by
  have hpole : poleTerm S c e = poleTerm S e c := by
    rw [poleTerm, poleTerm]; ring
  have hdiag : diagTerm S c e = diagTerm S e c :=
    sum_congr rfl fun n _ => by ring
  have hjet : jetTerm S c e = jetTerm S e c := by
    rw [jetTerm, jetTerm]
    rw [Finset.sum_comm' (s' := fun m => S.erase m) (t' := S) (fun n m => by
      simp only [mem_erase]; tauto)]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by
      rw [jetKernel_comm]; ring
  have hcont : contactTerm w S c e = contactTerm w S e c := by
    rw [contactTerm, contactTerm]
    rw [Finset.sum_comm' (s' := fun m => S.erase m) (t' := S) (fun n m => by
      simp only [mem_erase]; tauto)]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by
      rw [contactW_comm]; ring
  rw [formBilinW, formBilinW, hpole, hdiag, hjet, hcont]

theorem combFormW_two_linear_comb (w : ℕ → ℝ) (S : Finset ℕ) (u v : ℕ → ℝ) (α β : ℝ) :
    combFormW w S (fun n => α * u n + β * v n) =
      α ^ 2 * combFormW w S u + 2 * α * β * formBilinW w S u v + β ^ 2 * combFormW w S v := by
  have hd1 : degOne S (fun n => α * u n + β * v n) = α * degOne S u + β * degOne S v := by
    simp only [degOne, add_div, sum_add_distrib, ← mul_sum, mul_div_assoc]
  have hd2 : degTwo S (fun n => α * u n + β * v n) = α * degTwo S u + β * degTwo S v := by
    simp only [degTwo, sum_add_distrib, ← mul_sum]
  have hdiag : diagTerm S (fun n => α * u n + β * v n) (fun n => α * u n + β * v n) =
      α ^ 2 * diagTerm S u u + 2 * α * β * diagTerm S u v + β ^ 2 * diagTerm S v v := by
    simp only [diagTerm, mul_sum]
    rw [← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  have hoff (K : ℕ → ℕ → ℝ) (hK : ∀ m n, K m n = K n m) :
      (∑ n ∈ S, ∑ m ∈ S.erase n, (α * u m + β * v m) * (α * u n + β * v n) * K m n) =
        α ^ 2 * (∑ n ∈ S, ∑ m ∈ S.erase n, u m * u n * K m n) +
          2 * α * β * (∑ n ∈ S, ∑ m ∈ S.erase n, u m * v n * K m n) +
          β ^ 2 * (∑ n ∈ S, ∑ m ∈ S.erase n, v m * v n * K m n) := by
    have hvu : (∑ n ∈ S, ∑ m ∈ S.erase n, v m * u n * K m n) =
        ∑ n ∈ S, ∑ m ∈ S.erase n, u m * v n * K m n := by
      rw [Finset.sum_comm' (s' := fun m => S.erase m) (t' := S) (fun n m => by
        simp only [mem_erase]; tauto)]
      exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by rw [hK]; ring
    have hexp : (∑ n ∈ S, ∑ m ∈ S.erase n, (α * u m + β * v m) * (α * u n + β * v n) * K m n) =
        α ^ 2 * (∑ n ∈ S, ∑ m ∈ S.erase n, u m * u n * K m n) +
          α * β * (∑ n ∈ S, ∑ m ∈ S.erase n, u m * v n * K m n) +
          α * β * (∑ n ∈ S, ∑ m ∈ S.erase n, v m * u n * K m n) +
          β ^ 2 * (∑ n ∈ S, ∑ m ∈ S.erase n, v m * v n * K m n) := by
      simp only [mul_sum]
      rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun n _ => ?_
      rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun m _ => by ring
    rw [hexp, hvu]
    ring
  rw [← formBilinW_self, ← formBilinW_self w S u, ← formBilinW_self w S v]
  unfold formBilinW poleTerm jetTerm contactTerm
  rw [hd1, hd2, hdiag, hoff jetKernel jetKernel_comm, hoff (contactW w) (contactW_comm w)]
  ring

/-- Nonnegativity on the entire two-dimensional span follows from `0 ≤ A`, `0 ≤ C`,
and `B^2 ≤ A C` without diagonalizing the `2 × 2` matrix. -/
theorem combFormW_two_span_nonneg_of_cauchy_schwarz {w : ℕ → ℝ} {S : Finset ℕ} {u v : ℕ → ℝ}
    (hA : 0 ≤ combFormW w S u) (hC : 0 ≤ combFormW w S v)
    (hCS : formBilinW w S u v ^ 2 ≤ combFormW w S u * combFormW w S v) (α β : ℝ) :
    0 ≤ combFormW w S (fun n => α * u n + β * v n) := by
  rw [combFormW_two_linear_comb]
  set A := combFormW w S u
  set C := combFormW w S v
  set B := formBilinW w S u v
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hB0 : B = 0 := by
      have : B ^ 2 ≤ 0 := by rw [← hA0] at hCS; linarith
      nlinarith [sq_nonneg B]
    rw [← hA0, hB0]
    nlinarith [sq_nonneg β]
  · have hmul : 0 ≤ A * (α ^ 2 * A + 2 * α * β * B + β ^ 2 * C) := by
      have hid : A * (α ^ 2 * A + 2 * α * β * B + β ^ 2 * C) =
          (α * A + β * B) ^ 2 + β ^ 2 * (A * C - B ^ 2) := by ring
      rw [hid]
      exact add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hCS))
    exact nonneg_of_mul_nonneg_right hmul hApos

/-! ### Count 1: Exact contact ratio bijection and the Liouville-twist shift -/

/-- On `S = Ioc N (N + 3KN)`, every off-diagonal contact has ratio `2 ≤ r ≤ 3K`,
identifying `contactTerm` with a sum over the divisor slices `combSlice N K r`. -/
theorem contactTerm_lateComb_eq (w : ℕ → ℝ) (N K : ℕ) (c e : ℕ → ℝ) :
    contactTerm w (Ioc N (N + 3 * K * N)) c e =
      ∑ r ∈ Icc 2 (3 * K), w r *
        ∑ m ∈ combSlice N K r, (c m * e (r * m) + c (r * m) * e m) := by
  set S := Ioc N (N + 3 * K * N)
  have hone (u v : ℕ → ℝ) :
      (∑ n ∈ S, ∑ m ∈ S.erase n, u m * v n * (if m ∣ n then w (n / m) else 0)) =
        ∑ r ∈ Icc 2 (3 * K), w r * ∑ m ∈ combSlice N K r, u m * v (r * m) := by
    rw [Finset.sum_comm' (s' := fun m => S.erase m) (t' := S) (fun n m => by
      simp only [mem_erase]; tauto)]
    have hinner : ∀ m ∈ S,
        ∑ n ∈ S.erase m, u m * v n * (if m ∣ n then w (n / m) else 0) =
          ∑ r ∈ Icc 2 (3 * K), if m ∈ combSlice N K r then w r * (u m * v (r * m)) else 0 := by
      intro m hm
      obtain ⟨hmN, _⟩ := mem_Ioc.mp hm
      have hm0 : 0 < m := by omega
      have hfilt : ∑ n ∈ S.erase m, u m * v n * (if m ∣ n then w (n / m) else 0) =
          ∑ n ∈ (S.erase m).filter (m ∣ ·), u m * v n * w (n / m) := by
        rw [sum_filter]
        exact sum_congr rfl fun n _ => by split_ifs <;> ring
      have hrhs : (∑ r ∈ Icc 2 (3 * K), if m ∈ combSlice N K r then w r * (u m * v (r * m)) else 0) =
          ∑ r ∈ (Icc 2 (3 * K)).filter (fun r => m ∈ combSlice N K r),
            w r * (u m * v (r * m)) := (sum_filter _ _).symm
      rw [hfilt, hrhs]
      refine sum_nbij' (fun n => n / m) (fun r => r * m) ?_ ?_ ?_ ?_ ?_
      · intro n hn
        obtain ⟨hnE, k, rfl⟩ := mem_filter.mp hn
        obtain ⟨hne, hnS⟩ := mem_erase.mp hnE
        obtain ⟨_, hn2⟩ := mem_Ioc.mp hnS
        rw [Nat.mul_div_cancel_left k hm0]
        have hk0 : k ≠ 0 := by
          rintro rfl
          have := (mem_Ioc.mp hnS).1
          omega
        have hk1 : k ≠ 1 := by rintro rfl; exact hne (mul_one m)
        have hk3K : k ≤ 3 * K := by
          by_contra hgt
          have : (N + 1) * (3 * K + 1) ≤ m * k := Nat.mul_le_mul hmN (by omega)
          nlinarith
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hk3K⟩, mem_Ioc.mpr ⟨hmN, ?_⟩⟩
        exact (Nat.le_div_iff_mul_le (by omega)).mpr hn2
      · intro r hr
        obtain ⟨hrI, hmSlice⟩ := mem_filter.mp hr
        obtain ⟨hr2, _⟩ := mem_Icc.mp hrI
        obtain ⟨_, hmtop⟩ := mem_Ioc.mp hmSlice
        refine mem_filter.mpr ⟨mem_erase.mpr ⟨?_, mem_Ioc.mpr ⟨by nlinarith, ?_⟩⟩, dvd_mul_left m r⟩
        · intro h
          have := Nat.eq_of_mul_eq_mul_right hm0 (h.trans (one_mul m).symm)
          omega
        · rw [mul_comm]
          exact (Nat.le_div_iff_mul_le (by omega)).mp hmtop
      · intro n hn
        rw [mul_comm]
        exact Nat.mul_div_cancel' (mem_filter.mp hn).2
      · intro r _
        exact Nat.mul_div_cancel r hm0
      · intro n hn
        rw [mul_comm _ m, Nat.mul_div_cancel' (mem_filter.mp hn).2]
        ring
    rw [sum_congr rfl hinner, sum_comm]
    refine sum_congr rfl fun r _ => ?_
    rw [mul_sum, ← sum_filter]
    have hsub : S.filter (fun m => m ∈ combSlice N K r) = combSlice N K r := by
      ext m
      dsimp only [S, combSlice]
      simp only [mem_filter, mem_Ioc]
      constructor
      · exact fun h => h.2
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2.trans (Nat.div_le_self _ _)⟩, h1, h2⟩
    rw [hsub]
  have hsplit : contactTerm w S c e =
      (∑ n ∈ S, ∑ m ∈ S.erase n, c m * e n * (if m ∣ n then w (n / m) else 0)) +
        ∑ n ∈ S, ∑ m ∈ S.erase n, e m * c n * (if m ∣ n then w (n / m) else 0) := by
    simp only [contactTerm, contactW, mul_add, sum_add_distrib]
    congr 1
    rw [Finset.sum_comm' (s' := fun m => S.erase m) (t' := S) (fun n m => by
      simp only [mem_erase]; tauto)]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  rw [hsplit, hone c e, hone e c, ← sum_add_distrib]
  refine sum_congr rfl fun r _ => ?_
  rw [← mul_add, ← sum_add_distrib]
  exact congrArg (w r * ·) (sum_congr rfl fun m _ => by ring)

theorem centeredMultiple_mul_of_coprime {d r : ℕ} (hc : Nat.Coprime d r) (m : ℕ) :
    centeredMultiple d (r * m) = centeredMultiple d m := by
  simp only [centeredMultiple]
  congr 1
  by_cases hdm : d ∣ m
  · simp [hdm, dvd_mul_of_dvd_right hdm r]
  · have hdrm : ¬ d ∣ r * m := fun h => hdm (hc.dvd_of_dvd_mul_left h)
    simp [hdm, hdrm]

/-- When `d_1` and `d_2` are coprime to every contact ratio `2 ≤ r ≤ 3K` (in particular
for all primes `p, q > 3K`), dilation by `r` preserves divisibility and reduces the
contact pairing on `S` to twice the weighted slice correlations. -/
theorem contactTerm_coprime_eq_slice_sum (w : ℕ → ℝ) (N K d₁ d₂ : ℕ)
    (hc₁ : ∀ r ∈ Icc 2 (3 * K), Nat.Coprime d₁ r)
    (hc₂ : ∀ r ∈ Icc 2 (3 * K), Nat.Coprime d₂ r) :
    contactTerm w (Ioc N (N + 3 * K * N)) (centeredMultiple d₁) (centeredMultiple d₂) =
      2 * ∑ r ∈ Icc 2 (3 * K), w r *
        ∑ m ∈ combSlice N K r, centeredMultiple d₁ m * centeredMultiple d₂ m := by
  rw [contactTerm_lateComb_eq, mul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hsum : (∑ m ∈ combSlice N K r,
        (centeredMultiple d₁ m * centeredMultiple d₂ (r * m) +
          centeredMultiple d₁ (r * m) * centeredMultiple d₂ m)) =
      2 * ∑ m ∈ combSlice N K r, centeredMultiple d₁ m * centeredMultiple d₂ m := by
    rw [mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [centeredMultiple_mul_of_coprime (hc₁ r hr), centeredMultiple_mul_of_coprime (hc₂ r hr)]
    ring
  rw [hsum]
  ring

/-- Replacing `Λ` by `SelectiveArithmetic.liouvilleWeight` on a coprime centered
divisibility mask leaves endpoint, diagonal, and jet terms unchanged and flips only
nonsquare contact ratios `2 ≤ r ≤ 3K` from `-Λ(r)` to `+Λ(r)`. -/
theorem combFormW_liouville_sub_combForm_coprime (N K d : ℕ)
    (hc : ∀ r ∈ Icc 2 (3 * K), Nat.Coprime d r) :
    combFormW SelectiveArithmetic.liouvilleWeight (Ioc N (N + 3 * K * N)) (centeredMultiple d) -
        combForm (Ioc N (N + 3 * K * N)) (centeredMultiple d) =
      4 * ∑ r ∈ (Icc 2 (3 * K)).filter (fun r => ¬ IsSquare r), (Λ r : ℝ) *
        ∑ m ∈ combSlice N K r, centeredMultiple d m ^ 2 := by
  classical
  set S := Ioc N (N + 3 * K * N)
  set v := centeredMultiple d
  have hdiff : combFormW SelectiveArithmetic.liouvilleWeight S v - combForm S v =
      contactTerm (fun k => (Λ k : ℝ)) S v v -
        contactTerm SelectiveArithmetic.liouvilleWeight S v v := by
    rw [← combFormW_vonMangoldt, ← formBilinW_self, ← formBilinW_self]
    unfold formBilinW
    ring
  rw [hdiff, contactTerm_coprime_eq_slice_sum _ N K d d hc hc,
    contactTerm_coprime_eq_slice_sum _ N K d d hc hc, ← mul_sub, ← sum_sub_distrib]
  have hsq : ∀ r : ℕ, ∑ m ∈ combSlice N K r, centeredMultiple d m * centeredMultiple d m =
      ∑ m ∈ combSlice N K r, v m ^ 2 :=
    fun r => sum_congr rfl fun m _ => (sq (v m)).symm
  simp only [hsq]
  rw [sum_filter]
  have hrew : (∑ r ∈ Icc 2 (3 * K),
        ((Λ r : ℝ) * ∑ m ∈ combSlice N K r, v m ^ 2 -
          SelectiveArithmetic.liouvilleWeight r * ∑ m ∈ combSlice N K r, v m ^ 2)) =
      ∑ r ∈ Icc 2 (3 * K),
        if ¬ IsSquare r then 2 * ((Λ r : ℝ) * ∑ m ∈ combSlice N K r, v m ^ 2) else 0 := by
    refine sum_congr rfl fun r _ => ?_
    unfold SelectiveArithmetic.liouvilleWeight
    by_cases hs : IsSquare r
    · simp [hs]
    · simp [hs]; ring
  rw [hrew]
  have hpull : (∑ r ∈ Icc 2 (3 * K),
        if ¬ IsSquare r then 2 * ((Λ r : ℝ) * ∑ m ∈ combSlice N K r, v m ^ 2) else 0) =
      2 * ∑ r ∈ Icc 2 (3 * K),
        if ¬ IsSquare r then (Λ r : ℝ) * ∑ m ∈ combSlice N K r, v m ^ 2 else 0 := by
    rw [mul_sum]
    exact sum_congr rfl fun r _ => by split_ifs <;> ring
  rw [hpull]
  ring

/-- For every `K ≥ 1`, `N ≥ 1`, and `d ≥ 2` coprime to `2..3K` (in particular every
prime `p > 3K`), the Liouville-twisted Weil form of `v_d` on `(N, N + 3KN]` is
strictly larger than the untwisted Weil form. -/
theorem combForm_lt_combFormW_liouville_coprime {N K d : ℕ}
    (hK : 1 ≤ K) (hN : 1 ≤ N) (hd : 2 ≤ d)
    (hc : ∀ r ∈ Icc 2 (3 * K), Nat.Coprime d r) :
    combForm (Ioc N (N + 3 * K * N)) (centeredMultiple d) <
      combFormW SelectiveArithmetic.liouvilleWeight (Ioc N (N + 3 * K * N)) (centeredMultiple d) := by
  classical
  rw [← sub_pos, combFormW_liouville_sub_combForm_coprime N K d hc]
  have h2notSq : ¬ IsSquare (2 : ℕ) := by
    rintro ⟨k, hk⟩
    rcases k with _ | _ | k
    · omega
    · omega
    · nlinarith
  have h2mem : 2 ∈ (Icc 2 (3 * K)).filter (fun r => ¬ IsSquare r) :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, by omega⟩, h2notSq⟩
  have hN1mem : N + 1 ∈ combSlice N K 2 := by
    refine mem_Ioc.mpr ⟨by omega, ?_⟩
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by nlinarith)
  have hvd_pos : 0 < centeredMultiple d (N + 1) ^ 2 := by
    apply sq_pos_of_ne_zero
    unfold centeredMultiple
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hdpos : (0 : ℝ) < 1 / d := by positivity
    have hdle : (1 : ℝ) / d ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hd2
    split_ifs <;> linarith
  have hslice_pos : 0 < ∑ m ∈ combSlice N K 2, centeredMultiple d m ^ 2 :=
    lt_of_lt_of_le hvd_pos (single_le_sum (fun _ _ => sq_nonneg _) hN1mem)
  have hterm2 : 0 < (Λ 2 : ℝ) * ∑ m ∈ combSlice N K 2, centeredMultiple d m ^ 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact mul_pos (Real.log_pos (by norm_num)) hslice_pos
  have hsum_pos : 0 < ∑ r ∈ (Icc 2 (3 * K)).filter (fun r => ¬ IsSquare r),
      (Λ r : ℝ) * ∑ m ∈ combSlice N K r, centeredMultiple d m ^ 2 :=
    lt_of_lt_of_le hterm2 (single_le_sum
      (f := fun r => (Λ r : ℝ) * ∑ m ∈ combSlice N K r, centeredMultiple d m ^ 2)
      (fun r _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (sum_nonneg fun _ _ => sq_nonneg _)) h2mem)
  linarith

/-! ### Count 2: Chinese Remainder shifted-incidence cancellation and mixed `O(log N)` bound -/

private theorem exists_residue_dvd_and_shift_dvd {d₁ d₂ : ℕ}
    (hd₂ : 0 < d₂) (hc : Nat.Coprime d₁ d₂) (h : ℕ) :
    ∃ r₀ : ℕ, ∀ m : ℕ, (d₁ ∣ m ∧ d₂ ∣ m + h) ↔ m % (d₁ * d₂) = r₀ % (d₁ * d₂) := by
  let cr := Nat.chineseRemainder hc 0 (d₂ - h % d₂)
  refine ⟨cr.1, fun m => ?_⟩
  have hr₁ : d₁ ∣ cr.1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have := cr.2.1
    rwa [Nat.ModEq, Nat.zero_mod] at this
  have hr₂ : d₂ ∣ cr.1 + h := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have hmod : (cr.1 + h) ≡ (d₂ - h % d₂) + h [MOD d₂] := cr.2.2.add_right h
    have hsum : (d₂ - h % d₂) + h = d₂ * (h / d₂ + 1) := by
      have hlt := Nat.mod_lt h hd₂
      have hdiv := Nat.div_add_mod h d₂
      rw [mul_add, mul_one]
      omega
    rw [Nat.ModEq, hsum, Nat.mul_mod_right] at hmod
    exact hmod
  constructor
  · rintro ⟨hm₁, hm₂⟩
    have hdist₁ : d₁ ∣ Nat.dist m cr.1 := by
      rcases le_total m cr.1 with hle | hle
      · rw [Nat.dist_eq_sub_of_le hle]; exact Nat.dvd_sub hr₁ hm₁
      · rw [Nat.dist_eq_sub_of_le_right hle]; exact Nat.dvd_sub hm₁ hr₁
    have hdist₂ : d₂ ∣ Nat.dist m cr.1 := by
      rcases le_total m cr.1 with hle | hle
      · have hle' : m + h ≤ cr.1 + h := Nat.add_le_add_right hle h
        have hsub : (cr.1 + h) - (m + h) = Nat.dist m cr.1 := by
          rw [Nat.dist_eq_sub_of_le hle]; omega
        rw [← hsub]
        exact Nat.dvd_sub hr₂ hm₂
      · have hle' : cr.1 + h ≤ m + h := Nat.add_le_add_right hle h
        have hsub : (m + h) - (cr.1 + h) = Nat.dist m cr.1 := by
          rw [Nat.dist_eq_sub_of_le_right hle]; omega
        rw [← hsub]
        exact Nat.dvd_sub hm₂ hr₂
    have hprod : d₁ * d₂ ∣ Nat.dist m cr.1 := hc.mul_dvd_of_dvd_of_dvd hdist₁ hdist₂
    rcases le_total m cr.1 with hle | hle
    · rw [Nat.dist_eq_sub_of_le hle] at hprod
      exact (Nat.modEq_iff_dvd' hle).mpr hprod
    · rw [Nat.dist_eq_sub_of_le_right hle] at hprod
      exact ((Nat.modEq_iff_dvd' hle).mpr hprod).symm
  · intro hmod
    have hprod : d₁ * d₂ ∣ Nat.dist m cr.1 := by
      rcases le_total m cr.1 with hle | hle
      · rw [Nat.dist_eq_sub_of_le hle]
        exact (Nat.modEq_iff_dvd' hle).mp hmod
      · rw [Nat.dist_eq_sub_of_le_right hle]
        exact (Nat.modEq_iff_dvd' hle).mp hmod.symm
    have hdist₁ : d₁ ∣ Nat.dist m cr.1 := dvd_trans (dvd_mul_right d₁ d₂) hprod
    have hdist₂ : d₂ ∣ Nat.dist m cr.1 := dvd_trans (dvd_mul_left d₂ d₁) hprod
    refine ⟨?_, ?_⟩
    · rcases le_total m cr.1 with hle | hle
      · rw [Nat.dist_eq_sub_of_le hle] at hdist₁
        have hr₁' : d₁ ∣ m + (cr.1 - m) := by rwa [Nat.add_sub_of_le hle]
        exact (Nat.dvd_add_iff_left hdist₁).mpr hr₁'
      · rw [Nat.dist_eq_sub_of_le_right hle] at hdist₁
        have heq : cr.1 + (m - cr.1) = m := Nat.add_sub_of_le hle
        exact heq ▸ dvd_add hr₁ hdist₁
    · rcases le_total m cr.1 with hle | hle
      · rw [Nat.dist_eq_sub_of_le hle] at hdist₂
        have heq : (m + h) + (cr.1 - m) = cr.1 + h := by omega
        exact (Nat.dvd_add_iff_left hdist₂).mpr (heq ▸ hr₂)
      · rw [Nat.dist_eq_sub_of_le_right hle] at hdist₂
        have heq : (cr.1 + h) + (m - cr.1) = m + h := by omega
        exact heq ▸ dvd_add hr₂ hdist₂

/-- Chinese Remainder shifted-incidence cancellation: for coprime `d_1, d_2 ≥ 1` and
every shift `h` and interval `(a, b]`, `|∑_{m ∈ (a, b]} v_{d_1}(m) v_{d_2}(m + h)| ≤ 2`. -/
theorem abs_sum_centeredMultiple_shift_le {d₁ d₂ : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hc : Nat.Coprime d₁ d₂) (h a b : ℕ) :
    |∑ m ∈ Ioc a b, centeredMultiple d₁ m * centeredMultiple d₂ (m + h)| ≤ 2 := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hd₁) with rfl | hd₁2
  · have hz : ∀ m, centeredMultiple 1 m = 0 := fun m => by simp [centeredMultiple]
    simp [hz]
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hd₂) with rfl | hd₂2
  · have hz : ∀ m, centeredMultiple 1 m = 0 := fun m => by simp [centeredMultiple]
    simp [hz]
  obtain ⟨r₀, hr₀⟩ := exists_residue_dvd_and_shift_dvd hd₂ hc h
  have hprod0 : 0 < d₁ * d₂ := Nat.mul_pos hd₁ hd₂
  have hpt (m : ℕ) :
      centeredMultiple d₁ m * centeredMultiple d₂ (m + h) =
        centeredResidue (d₁ * d₂) r₀ m -
          (1 / (d₂ : ℝ)) * centeredMultiple d₁ m -
          (1 / (d₁ : ℝ)) * centeredMultiple d₂ (m + h) := by
    have hiff := hr₀ m
    simp only [centeredMultiple, centeredResidue, hprod0.ne', if_false, Nat.cast_mul]
    by_cases h1 : d₁ ∣ m <;> by_cases h2 : d₂ ∣ m + h
    · have hm : m % (d₁ * d₂) = r₀ % (d₁ * d₂) := hiff.mp ⟨h1, h2⟩
      simp only [h1, h2, hm, if_true, one_div, mul_inv]
      ring
    · have hm : m % (d₁ * d₂) ≠ r₀ % (d₁ * d₂) := fun hm => h2 (hiff.mpr hm).2
      simp only [h1, h2, hm, if_true, if_false, one_div, mul_inv]
      ring
    · have hm : m % (d₁ * d₂) ≠ r₀ % (d₁ * d₂) := fun hm => h1 (hiff.mpr hm).1
      simp only [h1, h2, hm, if_true, if_false, one_div, mul_inv]
      ring
    · have hm : m % (d₁ * d₂) ≠ r₀ % (d₁ * d₂) := fun hm => h1 (hiff.mpr hm).1
      simp only [h1, h2, hm, if_false, one_div, mul_inv]
      ring
  have hsum : ∑ m ∈ Ioc a b, centeredMultiple d₁ m * centeredMultiple d₂ (m + h) =
      (∑ m ∈ Ioc a b, centeredResidue (d₁ * d₂) r₀ m) -
        (1 / (d₂ : ℝ)) * (∑ m ∈ Ioc a b, centeredMultiple d₁ m) -
        (1 / (d₁ : ℝ)) * (∑ m ∈ Ioc a b, centeredMultiple d₂ (m + h)) := by
    simp only [hpt, sum_sub_distrib, ← mul_sum]
  have hshift : ∑ m ∈ Ioc a b, centeredMultiple d₂ (m + h) =
      ∑ k ∈ Ioc (a + h) (b + h), centeredMultiple d₂ k := by
    refine sum_nbij' (· + h) (· - h) ?_ ?_ ?_ ?_ ?_
    · intro m hm; obtain ⟨h1, h2⟩ := mem_Ioc.mp hm; exact mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro k hk; obtain ⟨h1, h2⟩ := mem_Ioc.mp hk; exact mem_Ioc.mpr ⟨by omega, by omega⟩
    · intro m _; omega
    · intro k hk; have := (mem_Ioc.mp hk).1; omega
    · intro _ _; rfl
  rw [hsum, hshift]
  have hb0 := abs_sum_centeredResidue_Ioc_le_one hprod0 r₀ a b
  have hb1 := abs_sum_centeredMultiple_Ioc_le_one hd₁ a b
  have hb2 := abs_sum_centeredMultiple_Ioc_le_one hd₂ (a + h) (b + h)
  have hd₁R : (2 : ℝ) ≤ d₁ := by exact_mod_cast hd₁2
  have hd₂R : (2 : ℝ) ≤ d₂ := by exact_mod_cast hd₂2
  have hi₁ : 1 / (d₁ : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hd₁R
  have hi₂ : 1 / (d₂ : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hd₂R
  have ht1 : |(1 / (d₂ : ℝ)) * ∑ m ∈ Ioc a b, centeredMultiple d₁ m| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc (1 / (d₂ : ℝ)) * |∑ m ∈ Ioc a b, centeredMultiple d₁ m|
        ≤ (1 / 2) * 1 := mul_le_mul hi₂ hb1 (abs_nonneg _) (by norm_num)
      _ = 1 / 2 := mul_one _
  have ht2 : |(1 / (d₁ : ℝ)) * ∑ k ∈ Ioc (a + h) (b + h), centeredMultiple d₂ k| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc (1 / (d₁ : ℝ)) * |∑ k ∈ Ioc (a + h) (b + h), centeredMultiple d₂ k|
        ≤ (1 / 2) * 1 := mul_le_mul hi₁ hb2 (abs_nonneg _) (by norm_num)
      _ = 1 / 2 := mul_one _
  have htri1 := abs_sub
    ((∑ m ∈ Ioc a b, centeredResidue (d₁ * d₂) r₀ m) -
      (1 / (d₂ : ℝ)) * ∑ m ∈ Ioc a b, centeredMultiple d₁ m)
    ((1 / (d₁ : ℝ)) * ∑ k ∈ Ioc (a + h) (b + h), centeredMultiple d₂ k)
  have htri2 := abs_sub
    (∑ m ∈ Ioc a b, centeredResidue (d₁ * d₂) r₀ m)
    ((1 / (d₂ : ℝ)) * ∑ m ∈ Ioc a b, centeredMultiple d₁ m)
  linarith

theorem abs_sum_centeredMultiple_shift_left_le {d₁ d₂ : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hc : Nat.Coprime d₁ d₂) (h a b : ℕ) :
    |∑ m ∈ Ioc a b, centeredMultiple d₁ (m + h) * centeredMultiple d₂ m| ≤ 2 := by
  have hcomm : (∑ m ∈ Ioc a b, centeredMultiple d₁ (m + h) * centeredMultiple d₂ m) =
      ∑ m ∈ Ioc a b, centeredMultiple d₂ m * centeredMultiple d₁ (m + h) :=
    sum_congr rfl fun _ _ => mul_comm _ _
  rw [hcomm]
  exact abs_sum_centeredMultiple_shift_le hd₂ hd₁ hc.symm h a b

theorem abs_sum_centeredMultiple_mul_Ioc_le {d₁ d₂ : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hc : Nat.Coprime d₁ d₂) (a b : ℕ) :
    |∑ m ∈ Ioc a b, centeredMultiple d₁ m * centeredMultiple d₂ m| ≤ 2 := by
  simpa using abs_sum_centeredMultiple_shift_le hd₁ hd₂ hc 0 a b

private theorem sum_harmonic_Icc_le (L : ℕ) :
    ∑ h ∈ Icc 1 L, 1 / (h : ℝ) ≤ 1 + Real.log L := by
  induction L with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hsplit : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
        ext h; simp only [mem_Icc, mem_insert]; omega
      rw [hsplit, sum_insert (by simp)]
      have hstep : 1 / ((n + 1 : ℕ) : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log n := by
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hlog := Real.log_le_sub_one_of_pos (div_pos hn0 hn1)
        rw [Real.log_div hn0.ne' hn1.ne'] at hlog
        have hdiff : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
          field_simp [hn1.ne']; ring
        rw [hdiff] at hlog
        push_cast
        linarith
      linarith

/-- Uniform mixed bilinear bound: on `S = Ioc N (N + 3KN)`, the mixed pairing of
`v_p` and `v_q` for any distinct primes `p ≠ q` is `O_{K, w}(1 + log N)`, with a
constant completely independent of `p`, `q`, and `N`. -/
theorem abs_formBilinW_distinct_primes_le (w : ℕ → ℝ) (N K : ℕ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    |formBilinW w (Ioc N (N + 3 * K * N)) (centeredMultiple p) (centeredMultiple q)| ≤
      (16 + 4 * (K : ℝ) + 4 * Real.log (1 + 3 * (K : ℝ)) +
        4 * ∑ r ∈ Icc 2 (3 * K), |w r|) * (1 + Real.log N) := by
  set S := Ioc N (N + 3 * K * N)
  set vp := centeredMultiple p
  set vq := centeredMultiple q
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hp0 : 0 < p := hp.pos
  have hq0 : 0 < q := hq.pos
  have hlogN_nn : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hlogK_nn : 0 ≤ Real.log (1 + 3 * (K : ℝ)) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ K from Nat.cast_nonneg K])
  have hw_nn : 0 ≤ ∑ r ∈ Icc 2 (3 * K), |w r| := sum_nonneg fun _ _ => abs_nonneg _
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hS0 : S = ∅ := by simp [S]
    simp only [hS0, formBilinW, poleTerm, diagTerm, jetTerm, contactTerm,
      degOne, degTwo, sum_empty, mul_zero, add_zero, sub_zero, abs_zero]
    positivity
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · have hS0 : S = ∅ := by simp [S]
    simp only [hS0, formBilinW, poleTerm, diagTerm, jetTerm, contactTerm,
      degOne, degTwo, sum_empty, mul_zero, add_zero, sub_zero, abs_zero]
    positivity
  -- 1. Endpoint (pole) term `≤ 2`
  have hpole : |poleTerm S vp vq| ≤ 2 := by
    have hd1 (d : ℕ) (hd : 0 < d) : |degOne S (centeredMultiple d)| ≤ 1 := by
      rw [degOne]
      have hrew : (∑ n ∈ S, centeredMultiple d n / (n : ℝ)) =
          ∑ n ∈ S, centeredResidue d 0 n / (n : ℝ) :=
        sum_congr rfl fun n _ => by rw [centeredMultiple_eq_centeredResidue hd]
      rw [hrew]
      refine (abs_sum_centeredResidue_harmonic_Ioc_le hd 0 N (N + 3 * K * N)).trans ?_
      exact div_le_one_of_le₀ (by linarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]) (by positivity)
    have hd2 (d : ℕ) (hd : 0 < d) : |degTwo S (centeredMultiple d)| ≤ 1 :=
      abs_sum_centeredMultiple_Ioc_le_one hd N (N + 3 * K * N)
    have h1 : |degOne S vp * degTwo S vq| ≤ 1 := by
      rw [abs_mul]; simpa using mul_le_mul (hd1 p hp0) (hd2 q hq0) (abs_nonneg _) zero_le_one
    have h2 : |degTwo S vp * degOne S vq| ≤ 1 := by
      rw [abs_mul]; simpa using mul_le_mul (hd2 p hp0) (hd1 q hq0) (abs_nonneg _) zero_le_one
    unfold poleTerm
    linarith [abs_add_le (degOne S vp * degTwo S vq) (degTwo S vp * degOne S vq)]
  -- 2. Diagonal term `≤ 12 + 2 log(1 + 3K) + 2 log N` via reversed Abel summation
  have hdiag : |diagTerm S vp vq| ≤
      12 + 2 * Real.log (1 + 3 * (K : ℝ)) + 2 * Real.log N := by
    set M := N + 3 * K * N
    set L := 3 * K * N
    have hsplit_ct : diagTerm S vp vq =
        (∑ n ∈ Ioc N M, vp n * vq n * Real.log n) -
          Real.log (2 * Real.pi) * ∑ n ∈ Ioc N M, vp n * vq n := by
      dsimp only [S, M]
      unfold diagTerm counterterm
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by have := (mem_Ioc.mp hn).1; exact_mod_cast (by omega : 0 < n)
      rw [Real.log_div hn0.ne' (by positivity)]
      ring
    have hconst : |Real.log (2 * Real.pi) * ∑ n ∈ Ioc N M, vp n * vq n| ≤ 12 := by
      have h2pi_pos : 0 < 2 * Real.pi := by positivity
      have hlog_nn : 0 ≤ Real.log (2 * Real.pi) :=
        Real.log_nonneg (by linarith [Real.pi_gt_three])
      have hlog_le : Real.log (2 * Real.pi) ≤ 6 := by
        have := Real.log_le_sub_one_of_pos h2pi_pos
        linarith [Real.pi_lt_d2]
      rw [abs_mul, abs_of_nonneg hlog_nn]
      have hc0 := abs_sum_centeredMultiple_mul_Ioc_le hp0 hq0 hc N M
      nlinarith [abs_nonneg (∑ n ∈ Ioc N M, vp n * vq n)]
    have hlog_part : |∑ n ∈ Ioc N M, vp n * vq n * Real.log n| ≤ 2 * Real.log M := by
      rw [← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range,
        show M + 1 - (N + 1) = L by omega]
      let wt : ℕ → ℝ := fun j => if j < L then Real.log ((M - j : ℕ) : ℝ) else 0
      have hrew : (∑ i ∈ range L, vp (N + 1 + i) * vq (N + 1 + i) * Real.log ((N + 1 + i : ℕ) : ℝ)) =
          ∑ j ∈ range L, wt j * (vp (N + 1 + (L - 1 - j)) * vq (N + 1 + (L - 1 - j))) := by
        rw [← sum_range_reflect]
        refine sum_congr rfl fun j hj => ?_
        have hjL := mem_range.mp hj
        have hidx : N + 1 + (L - 1 - j) = M - j := by omega
        simp only [wt, hjL, if_true, hidx]
        ring
      rw [hrew]
      have hab := HTGeometry.abs_sum_reversed_mul_le
        (g := fun i => vp (N + 1 + i) * vq (N + 1 + i))
        (w := wt) (B := 2) L
        (fun u v huv => by
          rw [sum_Ico_eq_sum_range]
          have hk := abs_sum_centeredMultiple_mul_Ioc_le hp0 hq0 hc (N + u) (N + v)
          rw [← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range,
            show N + v + 1 - (N + u + 1) = v - u by omega] at hk
          refine (le_of_eq (congrArg abs (sum_congr rfl fun x _ => ?_))).trans hk
          rw [show N + 1 + (u + x) = N + u + 1 + x by omega])
        (fun j => by
          dsimp [wt]
          split_ifs
          · exact Real.log_natCast_nonneg _
          · exact le_rfl)
        (fun j => by
          dsimp [wt]
          by_cases hj1 : j + 1 < L
          · rw [if_pos hj1, if_pos (by omega)]
            exact Real.log_le_log (by exact_mod_cast (by omega : 0 < M - (j + 1)))
              (by exact_mod_cast (show M - (j + 1) ≤ M - j by omega))
          · rw [if_neg hj1]
            split_ifs
            · exact Real.log_natCast_nonneg _
            · exact le_rfl)
      have hL0 : 0 < L := by positivity
      simpa [wt, hL0] using hab
    have hlogM : Real.log (M : ℝ) = Real.log (1 + 3 * (K : ℝ)) + Real.log N := by
      have hM : (M : ℝ) = (1 + 3 * (K : ℝ)) * N := by dsimp [M]; push_cast; ring
      rw [hM, Real.log_mul (by positivity) (by positivity)]
    rw [hsplit_ct]
    have htri := abs_sub (∑ n ∈ Ioc N M, vp n * vq n * Real.log n)
      (Real.log (2 * Real.pi) * ∑ n ∈ Ioc N M, vp n * vq n)
    linarith
  -- 3. Contact term `≤ 4 * ∑_{r=2}^{3K} |w r|`
  have hcont : |contactTerm w S vp vq| ≤ 4 * ∑ r ∈ Icc 2 (3 * K), |w r| := by
    rw [contactTerm_lateComb_eq]
    have hslice_one (d₁ d₂ : ℕ) (hd₁ : d₁.Prime) (hd₂ : d₂.Prime) (hne : d₁ ≠ d₂) (r : ℕ) :
        |∑ m ∈ combSlice N K r, centeredMultiple d₁ m * centeredMultiple d₂ (r * m)| ≤ 2 := by
      have hc12 : Nat.Coprime d₁ d₂ := (Nat.coprime_primes hd₁ hd₂).mpr hne
      by_cases hdr : d₂ ∣ r
      · have hconst_d : ∀ m, centeredMultiple d₂ (r * m) = 1 - 1 / (d₂ : ℝ) := fun m => by
          simp [centeredMultiple, dvd_mul_of_dvd_left hdr m]
        have hrew : (∑ m ∈ combSlice N K r, centeredMultiple d₁ m * centeredMultiple d₂ (r * m)) =
            (1 - 1 / (d₂ : ℝ)) * ∑ m ∈ combSlice N K r, centeredMultiple d₁ m := by
          rw [mul_sum]
          exact sum_congr rfl fun m _ => by rw [hconst_d]; ring
        rw [hrew, abs_mul]
        have hd₂2 : (2 : ℝ) ≤ d₂ := by exact_mod_cast hd₂.two_le
        have hfac : |1 - 1 / (d₂ : ℝ)| ≤ 1 := by
          have : 0 ≤ 1 / (d₂ : ℝ) ∧ 1 / (d₂ : ℝ) ≤ 1 :=
            ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith)⟩
          rw [abs_le]; constructor <;> linarith
        calc |1 - 1 / (d₂ : ℝ)| * |∑ m ∈ combSlice N K r, centeredMultiple d₁ m|
            ≤ 1 * 1 := mul_le_mul hfac
              (abs_sum_centeredMultiple_Ioc_le_one hd₁.pos _ _) (abs_nonneg _) zero_le_one
          _ ≤ 2 := by norm_num
      · have hcop : Nat.Coprime d₂ r := hd₂.coprime_iff_not_dvd.mpr hdr
        have hrew : (∑ m ∈ combSlice N K r, centeredMultiple d₁ m * centeredMultiple d₂ (r * m)) =
            ∑ m ∈ combSlice N K r, centeredMultiple d₁ m * centeredMultiple d₂ m :=
          sum_congr rfl fun m _ => by rw [centeredMultiple_mul_of_coprime hcop]
        rw [hrew]
        exact abs_sum_centeredMultiple_mul_Ioc_le hd₁.pos hd₂.pos hc12 _ _
    calc |∑ r ∈ Icc 2 (3 * K), w r * ∑ m ∈ combSlice N K r, (vp m * vq (r * m) + vp (r * m) * vq m)|
        ≤ ∑ r ∈ Icc 2 (3 * K),
            |w r * ∑ m ∈ combSlice N K r, (vp m * vq (r * m) + vp (r * m) * vq m)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Icc 2 (3 * K), |w r| * 4 := by
          refine sum_le_sum fun r _ => ?_
          rw [abs_mul, sum_add_distrib]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have h1 := hslice_one p q hp hq hpq r
          have h2 : |∑ m ∈ combSlice N K r, vp (r * m) * vq m| ≤ 2 := by
            have hcomm : (∑ m ∈ combSlice N K r, vp (r * m) * vq m) =
                ∑ m ∈ combSlice N K r, vq m * vp (r * m) :=
              sum_congr rfl fun _ _ => mul_comm _ _
            rw [hcomm]
            exact hslice_one q p hq hp hpq.symm r
          linarith [abs_add_le (∑ m ∈ combSlice N K r, vp m * vq (r * m))
            (∑ m ∈ combSlice N K r, vp (r * m) * vq m)]
      _ = 4 * ∑ r ∈ Icc 2 (3 * K), |w r| := by rw [← sum_mul, mul_comm]
  -- 4. Jet term `≤ 2 + 2 log(3KN) + (3/2) K` via shift grouping + smooth Abel bound
  have hjet : |jetTerm S vp vq| ≤
      2 + 2 * Real.log (1 + 3 * (K : ℝ)) + 2 * Real.log N + 2 * (K : ℝ) := by
    set M := N + 3 * K * N
    set L := 3 * K * N
    have hsplit_j : jetTerm S vp vq =
        (∑ n ∈ S, ∑ m ∈ S.erase n, vp m * vq n * (1 / (2 * |(m : ℝ) - n|))) +
          ∑ n ∈ S, ∑ m ∈ S.erase n, vp m * vq n * (1 / (2 * ((m : ℝ) + n))) := by
      unfold jetTerm
      simp only [jetKernel_eq_add_halves, mul_add, sum_add_distrib]
    -- 4a. Smooth kernel `1 / (2 * (m + n))` bounded by `(3 / 2) * K`
    have hreg : |∑ n ∈ S, ∑ m ∈ S.erase n, vp m * vq n * (1 / (2 * ((m : ℝ) + n)))| ≤
        2 * (K : ℝ) := by
      have hrow : ∀ n ∈ S, |∑ m ∈ S.erase n, vp m * vq n * (1 / (2 * ((m : ℝ) + n)))| ≤
          2 / (4 * ((N : ℝ) + 1)) := by
        intro n hn
        have hnS : n ∈ S := hn
        have hadd_diag : (∑ m ∈ S.erase n, vp m * vq n * (1 / (2 * ((m : ℝ) + n)))) =
            vq n * (∑ m ∈ S, vp m * (1 / (2 * ((m : ℝ) + n)))) -
              vp n * vq n * (1 / (2 * ((n : ℝ) + n))) := by
          have hins := add_sum_erase S (fun m => vp m * vq n * (1 / (2 * ((m : ℝ) + n)))) hnS
          have hmul : ∑ m ∈ S, vp m * vq n * (1 / (2 * ((m : ℝ) + n))) =
              vq n * ∑ m ∈ S, vp m * (1 / (2 * ((m : ℝ) + n))) := by
            rw [mul_sum]
            exact sum_congr rfl fun m _ => by ring
          linarith
        have hfull : |∑ m ∈ S, vp m * (1 / (2 * ((m : ℝ) + n)))| ≤ 1 / (4 * ((N : ℝ) + 1)) := by
          dsimp [S]
          rw [← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range,
            show M + 1 - (N + 1) = L by omega]
          have hcomm : (∑ i ∈ range L, vp (N + 1 + i) * (1 / (2 * (((N + 1 + i : ℕ) : ℝ) + n)))) =
              ∑ i ∈ range L, (1 / (2 * (((N + 1 + i : ℕ) : ℝ) + n))) * vp (N + 1 + i) :=
            sum_congr rfl fun _ _ => mul_comm _ _
          rw [hcomm]
          have hab := HTGeometry.abs_sum_mul_le_of_finite_partial
            (g := fun i => vp (N + 1 + i))
            (w := fun i => 1 / (2 * (((N + 1 + i : ℕ) : ℝ) + n))) (B := 1) L
            (fun k _ => by
              have hk := abs_sum_centeredMultiple_Ioc_le_one hp0 N (N + k)
              rwa [← AbsoluteGeometryOfSpecZ.Ico_succ_succ_eq_Ioc', sum_Ico_eq_sum_range,
                show N + k + 1 - (N + 1) = k by omega] at hk)
            (fun _ => by positivity)
            (fun i => one_div_le_one_div_of_le (by positivity) (by push_cast; linarith))
          have hn1 : (N : ℝ) + 1 ≤ n := by
            have := (mem_Ioc.mp hn).1
            exact_mod_cast this
          refine hab.trans ?_
          rw [one_mul]
          exact one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
        have hdiag_n : |vp n * vq n * (1 / (2 * ((n : ℝ) + n)))| ≤ 1 / (4 * ((N : ℝ) + 1)) := by
          rw [abs_mul, abs_mul]
          have hv1 := abs_centeredMultiple_le_one hp0 n
          have hv2 := abs_centeredMultiple_le_one hq0 n
          have hn1 : (N : ℝ) + 1 ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1
          have hw : |1 / (2 * ((n : ℝ) + n))| ≤ 1 / (4 * ((N : ℝ) + 1)) := by
            rw [abs_of_nonneg (by positivity)]
            exact one_div_le_one_div_of_le (by positivity) (by linarith)
          have hprod1 : |vp n| * |vq n| ≤ 1 := by
            simpa using mul_le_mul hv1 hv2 (abs_nonneg _) zero_le_one
          calc |vp n| * |vq n| * |1 / (2 * ((n : ℝ) + n))|
              ≤ 1 * (1 / (4 * ((N : ℝ) + 1))) :=
                mul_le_mul hprod1 hw (abs_nonneg _) (by positivity)
            _ = 1 / (4 * ((N : ℝ) + 1)) := one_mul _
        have hvq1 := abs_centeredMultiple_le_one hq0 n
        have hvfull : |vq n * ∑ m ∈ S, vp m * (1 / (2 * ((m : ℝ) + n)))| ≤
            1 / (4 * ((N : ℝ) + 1)) := by
          rw [abs_mul]
          calc |vq n| * |∑ m ∈ S, vp m * (1 / (2 * ((m : ℝ) + n)))|
              ≤ 1 * (1 / (4 * ((N : ℝ) + 1))) :=
                mul_le_mul hvq1 hfull (abs_nonneg _) (by positivity)
            _ = 1 / (4 * ((N : ℝ) + 1)) := one_mul _
        rw [hadd_diag, show (2 : ℝ) / (4 * ((N : ℝ) + 1)) =
          1 / (4 * ((N : ℝ) + 1)) + 1 / (4 * ((N : ℝ) + 1)) by ring]
        have htri := abs_sub (vq n * ∑ m ∈ S, vp m * (1 / (2 * ((m : ℝ) + n))))
          (vp n * vq n * (1 / (2 * ((n : ℝ) + n))))
        linarith
      calc |∑ n ∈ S, ∑ m ∈ S.erase n, vp m * vq n * (1 / (2 * ((m : ℝ) + n)))|
          ≤ ∑ n ∈ S, |∑ m ∈ S.erase n, vp m * vq n * (1 / (2 * ((m : ℝ) + n)))| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ S, (2 / (4 * ((N : ℝ) + 1))) := sum_le_sum hrow
        _ = (3 * (K : ℝ) * N) * (2 / (4 * ((N : ℝ) + 1))) := by
            dsimp [S]
            rw [sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left, nsmul_eq_mul]
            push_cast; ring
        _ ≤ 2 * (K : ℝ) := by
            rw [div_eq_mul_inv]
            have hle : (3 * (K : ℝ) * N) * (2 * (4 * ((N : ℝ) + 1))⁻¹) ≤ 2 * (K : ℝ) := by
              rw [show (3 * (K : ℝ) * N) * (2 * (4 * ((N : ℝ) + 1))⁻¹) =
                (6 * (K : ℝ) * N) / (4 * ((N : ℝ) + 1)) by ring]
              rw [div_le_iff₀ (by positivity)]
              nlinarith [show (0 : ℝ) ≤ K by positivity, show (0 : ℝ) ≤ N by positivity]
            exact hle
    -- 4b. Singular kernel `1 / (2 * |m - n|)` grouped by `h = |m - n|`
    have hsing : |∑ n ∈ S, ∑ m ∈ S.erase n, vp m * vq n * (1 / (2 * |(m : ℝ) - n|))| ≤
        2 + 2 * Real.log (1 + 3 * (K : ℝ)) + 2 * Real.log N := by
      have htri_part : ∀ n ∈ S, S.erase n = (S.filter (· < n)) ∪ (S.filter (n < ·)) := by
        intro n _
        ext m
        simp only [mem_erase, mem_union, mem_filter]
        by_cases hmS : m ∈ S
        · simp only [hmS, and_true, true_and]; omega
        · simp [hmS]
      have htri_disj : ∀ n : ℕ, Disjoint (S.filter (· < n)) (S.filter (n < ·)) := by
        intro n
        rw [disjoint_filter]
        intro m _ h1 h2; omega
      have hsplit_ul : (∑ n ∈ S, ∑ m ∈ S.erase n, vp m * vq n * (1 / (2 * |(m : ℝ) - n|))) =
          (∑ n ∈ S, ∑ m ∈ S.filter (· < n), vp m * vq n * (1 / (2 * |(m : ℝ) - n|))) +
            ∑ m ∈ S, ∑ n ∈ S.filter (· < m), vp m * vq n * (1 / (2 * |(m : ℝ) - n|)) := by
        have hrow_split : ∀ n ∈ S,
            (∑ m ∈ S.erase n, vp m * vq n * (1 / (2 * |(m : ℝ) - n|))) =
              (∑ m ∈ S.filter (· < n), vp m * vq n * (1 / (2 * |(m : ℝ) - n|))) +
                ∑ m ∈ S.filter (n < ·), vp m * vq n * (1 / (2 * |(m : ℝ) - n|)) :=
          fun n hn => by rw [htri_part n hn, sum_union (htri_disj n)]
        rw [sum_congr rfl hrow_split, sum_add_distrib]
        congr 1
        exact Finset.sum_comm' (s' := fun m => S.filter (· < m)) (t' := S) fun n m => by
          simp only [mem_filter]; tauto
      have hhalf_shift (u v : ℕ → ℝ) :
          (∑ b ∈ S, ∑ a ∈ S.filter (· < b), u a * v b * (1 / (2 * |(a : ℝ) - b|))) =
            ∑ h ∈ Icc 1 L, (1 / (2 * (h : ℝ))) * ∑ a ∈ Ioc N (M - h), u a * v (a + h) := by
        rw [Finset.sum_comm' (s' := fun a => S.filter (a < ·)) (t' := S) (fun b a => by
          simp only [mem_filter]; tauto)]
        have hinner : ∀ a ∈ S,
            (∑ b ∈ S.filter (a < ·), u a * v b * (1 / (2 * |(a : ℝ) - b|))) =
              ∑ h ∈ Icc 1 L, if a ∈ Ioc N (M - h) then (1 / (2 * (h : ℝ))) * (u a * v (a + h)) else 0 := by
          intro a ha
          obtain ⟨haN, _⟩ := mem_Ioc.mp ha
          have hrhs : (∑ h ∈ Icc 1 L,
                if a ∈ Ioc N (M - h) then (1 / (2 * (h : ℝ))) * (u a * v (a + h)) else 0) =
              ∑ h ∈ (Icc 1 L).filter (fun h => a ∈ Ioc N (M - h)),
                (1 / (2 * (h : ℝ))) * (u a * v (a + h)) := (sum_filter _ _).symm
          rw [hrhs]
          refine sum_nbij' (fun b => b - a) (fun h => a + h) ?_ ?_ ?_ ?_ ?_
          · intro b hb
            obtain ⟨hbS, hab⟩ := mem_filter.mp hb
            obtain ⟨_, hbM⟩ := mem_Ioc.mp hbS
            exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, mem_Ioc.mpr ⟨haN, by omega⟩⟩
          · intro h hh
            obtain ⟨hhI, haI⟩ := mem_filter.mp hh
            obtain ⟨hh1, _⟩ := mem_Icc.mp hhI
            obtain ⟨_, haMh⟩ := mem_Ioc.mp haI
            exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro b hb; have := (mem_filter.mp hb).2; omega
          · intro h _; omega
          · intro b hb
            have hab := (mem_filter.mp hb).2
            have hba : a + (b - a) = b := by omega
            have hdiff : (a : ℝ) - b = -((b - a : ℕ) : ℝ) := by
              rw [Nat.cast_sub hab.le]; ring
            rw [hba, hdiff, abs_neg, abs_of_pos (by exact_mod_cast Nat.sub_pos_of_lt hab)]
            ring
        rw [sum_congr rfl hinner, sum_comm]
        refine sum_congr rfl fun h _ => ?_
        rw [mul_sum, ← sum_filter]
        have hsub : S.filter (fun a => a ∈ Ioc N (M - h)) = Ioc N (M - h) := by
          ext a
          dsimp only [S, M]
          simp only [mem_filter, mem_Ioc]
          constructor
          · exact fun h' => h'.2
          · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, h1, h2⟩
        rw [hsub]
      have h1 : |∑ n ∈ S, ∑ m ∈ S.filter (· < n), vp m * vq n * (1 / (2 * |(m : ℝ) - n|))| ≤
          ∑ h ∈ Icc 1 L, 1 / (h : ℝ) := by
        rw [hhalf_shift vp vq]
        calc |∑ h ∈ Icc 1 L, (1 / (2 * (h : ℝ))) * ∑ a ∈ Ioc N (M - h), vp a * vq (a + h)|
            ≤ ∑ h ∈ Icc 1 L, |(1 / (2 * (h : ℝ))) * ∑ a ∈ Ioc N (M - h), vp a * vq (a + h)| :=
              abs_sum_le_sum_abs _ _
          _ ≤ ∑ h ∈ Icc 1 L, 1 / (h : ℝ) := by
              refine sum_le_sum fun h hh => ?_
              have hh0 : (0 : ℝ) < h := by exact_mod_cast (mem_Icc.mp hh).1
              rw [abs_mul, abs_of_pos (by positivity)]
              have hsh := abs_sum_centeredMultiple_shift_le hp0 hq0 hc h N (M - h)
              calc (1 / (2 * (h : ℝ))) * |∑ a ∈ Ioc N (M - h), vp a * vq (a + h)|
                  ≤ (1 / (2 * (h : ℝ))) * 2 :=
                    mul_le_mul_of_nonneg_left hsh (by positivity)
                _ = 1 / (h : ℝ) := by ring
      have h2 : |∑ m ∈ S, ∑ n ∈ S.filter (· < m), vp m * vq n * (1 / (2 * |(m : ℝ) - n|))| ≤
          ∑ h ∈ Icc 1 L, 1 / (h : ℝ) := by
        have hrew : (∑ m ∈ S, ∑ n ∈ S.filter (· < m), vp m * vq n * (1 / (2 * |(m : ℝ) - n|))) =
            ∑ m ∈ S, ∑ n ∈ S.filter (· < m), vq n * vp m * (1 / (2 * |(n : ℝ) - m|)) :=
          sum_congr rfl fun m _ => sum_congr rfl fun n _ => by
            rw [abs_sub_comm]; ring
        rw [hrew, hhalf_shift vq vp]
        calc |∑ h ∈ Icc 1 L, (1 / (2 * (h : ℝ))) * ∑ a ∈ Ioc N (M - h), vq a * vp (a + h)|
            ≤ ∑ h ∈ Icc 1 L, |(1 / (2 * (h : ℝ))) * ∑ a ∈ Ioc N (M - h), vq a * vp (a + h)| :=
              abs_sum_le_sum_abs _ _
          _ ≤ ∑ h ∈ Icc 1 L, 1 / (h : ℝ) := by
              refine sum_le_sum fun h hh => ?_
              have hh0 : (0 : ℝ) < h := by exact_mod_cast (mem_Icc.mp hh).1
              rw [abs_mul, abs_of_pos (by positivity)]
              have hsh := abs_sum_centeredMultiple_shift_le hq0 hp0 hc.symm h N (M - h)
              calc (1 / (2 * (h : ℝ))) * |∑ a ∈ Ioc N (M - h), vq a * vp (a + h)|
                  ≤ (1 / (2 * (h : ℝ))) * 2 :=
                    mul_le_mul_of_nonneg_left hsh (by positivity)
                _ = 1 / (h : ℝ) := by ring
      have hharm := sum_harmonic_Icc_le L
      have hlogL : Real.log (L : ℝ) ≤ Real.log (1 + 3 * (K : ℝ)) + Real.log N := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        refine Real.log_le_log (by positivity) ?_
        dsimp [L]
        push_cast
        linarith
      rw [hsplit_ul]
      have htri := abs_add_le
        (∑ n ∈ S, ∑ m ∈ S.filter (· < n), vp m * vq n * (1 / (2 * |(m : ℝ) - n|)))
        (∑ m ∈ S, ∑ n ∈ S.filter (· < m), vp m * vq n * (1 / (2 * |(m : ℝ) - n|)))
      linarith
    rw [hsplit_j]
    have htri := abs_add_le
      (∑ n ∈ S, ∑ m ∈ S.erase n, vp m * vq n * (1 / (2 * |(m : ℝ) - n|)))
      (∑ n ∈ S, ∑ m ∈ S.erase n, vp m * vq n * (1 / (2 * ((m : ℝ) + n))))
    linarith
  -- Assemble all four bounds
  unfold formBilinW
  have ht1 := abs_sub (poleTerm S vp vq + diagTerm S vp vq - jetTerm S vp vq) (contactTerm w S vp vq)
  have ht2 := abs_sub (poleTerm S vp vq + diagTerm S vp vq) (jetTerm S vp vq)
  have ht3 := abs_add_le (poleTerm S vp vq) (diagTerm S vp vq)
  have htot : |poleTerm S vp vq + diagTerm S vp vq - jetTerm S vp vq - contactTerm w S vp vq| ≤
      16 + 2 * (K : ℝ) + 4 * Real.log (1 + 3 * (K : ℝ)) +
        4 * (∑ r ∈ Icc 2 (3 * K), |w r|) + 4 * Real.log N := by
    linarith
  set C₀ := 16 + 4 * (K : ℝ) + 4 * Real.log (1 + 3 * (K : ℝ)) +
    4 * ∑ r ∈ Icc 2 (3 * K), |w r|
  have hC₀_ge : 16 ≤ C₀ := by
    dsimp [C₀]
    linarith [show (0 : ℝ) ≤ K by positivity]
  have hlog_part2 : 4 * Real.log N ≤ C₀ * Real.log N :=
    mul_le_mul_of_nonneg_right (by linarith) hlogN_nn
  have hexp : C₀ * (1 + Real.log N) = C₀ + C₀ * Real.log N := by ring
  rw [hexp]
  dsimp [C₀] at htot ⊢
  linarith [show (0 : ℝ) ≤ K by positivity]

/-! ### Count 3: Shifted-period variance bounds on intervals -/

private theorem sum_centeredMultiple_sq_shifted_period {d : ℕ} (hd : 0 < d) (A : ℕ) :
    ∑ n ∈ Ioc A (A + d), centeredMultiple d n ^ 2 = 1 - 1 / (d : ℝ) := by
  have hdvd : (Ioc A (A + d)).filter (d ∣ ·) =
      (Ioc A (A + d)).filter (fun n => n % d = 0 % d) := by
    ext n; simp [Nat.dvd_iff_mod_eq_zero]
  have hc1 : ((Ioc A (A + d)).filter (d ∣ ·)).card = 1 := by
    rw [hdvd]
    simpa only [mul_one] using card_Ioc_mod_eq hd 0 A 1
  have hsplit : ∑ n ∈ Ioc A (A + d), centeredMultiple d n ^ 2 =
      (∑ n ∈ (Ioc A (A + d)).filter (d ∣ ·), centeredMultiple d n ^ 2) +
        ∑ n ∈ (Ioc A (A + d)).filter (fun n => ¬ d ∣ n), centeredMultiple d n ^ 2 :=
    (sum_filter_add_sum_filter_not (Ioc A (A + d)) (d ∣ ·) _).symm
  have h1 : ∀ n ∈ (Ioc A (A + d)).filter (d ∣ ·),
      centeredMultiple d n ^ 2 = (1 - 1 / (d : ℝ)) ^ 2 := fun n hn => by
    rw [centeredMultiple, if_pos (mem_filter.mp hn).2]
  have h2 : ∀ n ∈ (Ioc A (A + d)).filter (fun n => ¬ d ∣ n),
      centeredMultiple d n ^ 2 = (1 / (d : ℝ)) ^ 2 := fun n hn => by
    rw [centeredMultiple, if_neg (mem_filter.mp hn).2, zero_sub, neg_sq]
  have hc2 : ((Ioc A (A + d)).filter (fun n => ¬ d ∣ n)).card = d - 1 := by
    have hcard := card_filter_add_card_filter_not (s := Ioc A (A + d)) (p := (d ∣ ·))
    rw [hc1, Nat.card_Ioc, Nat.add_sub_cancel_left] at hcard
    omega
  rw [hsplit, sum_congr rfl h1, sum_congr rfl h2, sum_const, sum_const, hc1, hc2,
    nsmul_eq_mul, nsmul_eq_mul, Nat.cast_one, Nat.cast_sub hd]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hd0]
  ring

private theorem sum_centeredMultiple_sq_periods {d : ℕ} (hd : 0 < d) (a q : ℕ) :
    ∑ n ∈ Ioc a (a + d * q), centeredMultiple d n ^ 2 =
      (q : ℝ) * (1 - 1 / (d : ℝ)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : Ioc a (a + d * (q + 1)) =
        Ioc a (a + d * q) ∪ Ioc (a + d * q) (a + d * q + d) := by
      rw [show a + d * (q + 1) = a + d * q + d by ring]
      exact (Ioc_union_Ioc_eq_Ioc (Nat.le_add_right a _) (Nat.le_add_right _ d)).symm
    rw [hsplit, sum_union (Ioc_disjoint_Ioc_of_le le_rfl), ih,
      sum_centeredMultiple_sq_shifted_period hd, Nat.cast_add, Nat.cast_one]
    ring

/-- Every interval `(a, b]` carries at least `⌊(b - a) / d⌋ (1 - 1/d)` of `ℓ^2` mass
for the centered divisibility indicator `v_d`. -/
theorem sum_centeredMultiple_sq_Ioc_ge {d : ℕ} (hd : 0 < d) (a b : ℕ) :
    (((b - a) / d : ℕ) : ℝ) * (1 - 1 / (d : ℝ)) ≤
      ∑ n ∈ Ioc a b, centeredMultiple d n ^ 2 := by
  rcases lt_or_ge b a with hlt | hab
  · have hba : b - a = 0 := Nat.sub_eq_zero_of_le hlt.le
    simp [hba, Ioc_eq_empty (not_lt.mpr hlt.le)]
  · set q := (b - a) / d
    have hsub : Ioc a (a + d * q) ⊆ Ioc a b :=
      Ioc_subset_Ioc_right ((Nat.add_le_add_left (Nat.mul_div_le (b - a) d) a).trans_eq
        (Nat.add_sub_of_le hab))
    rw [← sum_centeredMultiple_sq_periods hd a q]
    exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _

/-- Companion upper bound: every interval `(a, b]` carries at most
`(⌊(b - a) / d⌋ + 1) (1 - 1/d)` of `ℓ^2` mass for `v_d`. -/
theorem sum_centeredMultiple_sq_Ioc_le {d : ℕ} (hd : 0 < d) (a b : ℕ) :
    ∑ n ∈ Ioc a b, centeredMultiple d n ^ 2 ≤
      ((((b - a) / d + 1 : ℕ)) : ℝ) * (1 - 1 / (d : ℝ)) := by
  have hd1 : 0 ≤ 1 - 1 / (d : ℝ) := by
    have : (1 : ℝ) / d ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hd)
    linarith
  rcases lt_or_ge b a with hlt | hab
  · simp only [Ioc_eq_empty (not_lt.mpr hlt.le), sum_empty]
    positivity
  · set q := (b - a) / d
    have hsub : Ioc a b ⊆ Ioc a (a + d * (q + 1)) :=
      Ioc_subset_Ioc_right ((Nat.add_sub_of_le hab).symm.le.trans
        (Nat.add_le_add_left (Nat.lt_mul_div_succ (b - a) hd).le a))
    rw [← sum_centeredMultiple_sq_periods hd a (q + 1)]
    exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _

#print axioms formBilinW_self
#print axioms combFormW_two_span_nonneg_of_cauchy_schwarz
#print axioms contactTerm_coprime_eq_slice_sum
#print axioms combFormW_liouville_sub_combForm_coprime
#print axioms combForm_lt_combFormW_liouville_coprime
#print axioms abs_sum_centeredMultiple_shift_le
#print axioms abs_formBilinW_distinct_primes_le
#print axioms sum_centeredMultiple_sq_Ioc_ge

end GaloisForLFunctions.SignedArithmeticCorrespondences
