import GaloisForLFunctions.HeckeLFunctions.HeckeHarmonicSumsSatisfyTheIdealHyperbolaIdentity

/-!
# The logarithmic derivative of a Hecke L-series runs over the powers of the prime ideals

For a ray class character `ψ` of a number field `K` put

`Λ_ψ(n) = Σ_{N𝔭^k = n} ψ(𝔭)^k log N𝔭`   (`heckeMangoldt`),

the sum over the powers of the nonzero prime ideals of norm `n`: the contacts of the ideals of
`K`, counted by their norms and twisted by `ψ`. Then on `Re s > 1`

`−L'/L(s, ψ) = Σ_n Λ_ψ(n) n^{−s}`   (`logDeriv_heckeL`),

absolutely convergent (`lSeriesSummable_heckeMangoldt`).

* **Convolution** (`log_mul_heckeCoeff_eq`). `log n · a_ψ(n) = Σ_{de = n} Λ_ψ(d) a_ψ(e)`, with
  `a_ψ(n) = Σ_{N𝔞 = n} ψ(𝔞)`: the ideal von Mangoldt identity of the corpus on the ideals of one
  norm, with the multiplicativity of `ψ`.
* **Size** (`norm_heckeMangoldt_le`). `|Λ_ψ(n)| ≤ log n · #{𝔞 : N𝔞 = n}`: a prime power is
  determined by its prime and its norm.
-/

noncomputable section

open Finset NumberField Ideal Filter
open scoped Classical

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions ArtinMertens

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- The von Mangoldt coefficients of a ray class character: `Σ_{N𝔭^k = n} ψ(𝔭)^k log N𝔭`. -/
def heckeMangoldt (ψ : HeckeCharacter 𝔪) (n : ℕ) : ℂ :=
  ∑ pk ∈ (primePowersLe K n).filter (fun pk => absNorm pk.1 ^ pk.2 = n),
    heckeValue 𝔪 ψ pk.1 ^ pk.2 * (Real.log (absNorm pk.1) : ℂ)

/-! ### Ideals of one norm -/

theorem filter_idealsLe_absNorm_eq {n x : ℕ} (hn : 1 ≤ n) (hnx : n ≤ x) :
    (idealsLe K x).filter (fun I => absNorm I = n) = idealsOfNorm K n := by
  ext I
  rw [mem_filter, mem_idealsLe, mem_idealsOfNorm]
  refine ⟨fun h => h.2, fun h => ⟨⟨fun h0 => ?_, h.le.trans hnx⟩, h⟩⟩
  rw [h0, absNorm_bot] at h
  omega

theorem filter_primePowersLe_eq {d n : ℕ} (hdn : d ≤ n) :
    (primePowersLe K d).filter (fun pk => absNorm pk.1 ^ pk.2 = d) =
      (primePowersLe K n).filter (fun pk => absNorm pk.1 ^ pk.2 = d) := by
  ext ⟨P, k⟩
  simp only [mem_filter, mem_primePowersLe]
  constructor
  · rintro ⟨⟨hP, hP0, hk, hle⟩, heq⟩
    exact ⟨⟨hP, hP0, hk, hle.trans hdn⟩, heq⟩
  · rintro ⟨⟨hP, hP0, hk, -⟩, heq⟩
    exact ⟨⟨hP, hP0, hk, heq.le⟩, heq⟩

/-- **The ideal von Mangoldt identity on the ideals of one norm.** -/
theorem sum_idealsOfNorm_mul_log (g : Ideal (𝓞 K) → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (∑ I ∈ idealsOfNorm K n, g I) * (Real.log n : ℂ) =
      ∑ pk ∈ primePowersLe K n, (Real.log (absNorm pk.1) : ℂ) *
        ∑ J ∈ idealsLe K (n / absNorm pk.1 ^ pk.2),
          if absNorm (pk.1 ^ pk.2 * J) = n then g (pk.1 ^ pk.2 * J) else 0 := by
  have h := sum_weight_mul_log_absNorm_idealsLe_eq (K := K)
    (fun I => if absNorm I = n then g I else 0) n
  rw [← h, ← filter_idealsLe_absNorm_eq hn le_rfl, Finset.sum_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs with hI
  · rw [hI]
  · rw [zero_mul]

/-! ### The convolution identity -/

/-- **`log · a_ψ = Λ_ψ ⋆ a_ψ`.** -/
theorem log_mul_heckeCoeff_eq (ψ : HeckeCharacter 𝔪) (n : ℕ) :
    (Real.log n : ℂ) * heckeCoeff 𝔪 ψ n =
      ∑ p ∈ n.divisorsAntidiagonal, heckeMangoldt 𝔪 ψ p.1 * heckeCoeff 𝔪 ψ p.2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : n ≠ 0 := hn.ne'
  -- the multiples of one prime power
  have hinner : ∀ pk ∈ primePowersLe K n,
      (∑ J ∈ idealsLe K (n / absNorm pk.1 ^ pk.2),
        if absNorm (pk.1 ^ pk.2 * J) = n then heckeValue 𝔪 ψ (pk.1 ^ pk.2 * J) else 0) =
      heckeValue 𝔪 ψ pk.1 ^ pk.2 *
        (if absNorm pk.1 ^ pk.2 ∣ n then heckeCoeff 𝔪 ψ (n / absNorm pk.1 ^ pk.2) else 0) := by
    rintro ⟨P, k⟩ hpk
    dsimp only
    obtain ⟨-, hP0, -, -⟩ := mem_primePowersLe.mp hpk
    have hd0 : 0 < absNorm P ^ k :=
      pow_pos (Nat.pos_of_ne_zero fun h => hP0 (absNorm_eq_zero_iff.mp h)) k
    have hterm : ∀ J : Ideal (𝓞 K),
        (if absNorm (P ^ k * J) = n then heckeValue 𝔪 ψ (P ^ k * J) else 0) =
        heckeValue 𝔪 ψ P ^ k *
          (if absNorm P ^ k * absNorm J = n then heckeValue 𝔪 ψ J else 0) := fun J => by
      rw [map_mul, map_pow, heckeValue_mul, heckeValue_pow]
      split_ifs with h
      · rfl
      · rw [mul_zero]
    simp only [hterm]
    rw [← Finset.mul_sum]
    congr 1
    by_cases hdvd : absNorm P ^ k ∣ n
    · rw [if_pos hdvd]
      have hq : 1 ≤ n / absNorm P ^ k := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd0
      rw [heckeCoeff, ← filter_idealsLe_absNorm_eq hq le_rfl, Finset.sum_filter]
      refine Finset.sum_congr rfl fun J _ => ?_
      have hiff : absNorm P ^ k * absNorm J = n ↔ absNorm J = n / absNorm P ^ k := by
        constructor
        · intro h
          rw [← h, Nat.mul_div_cancel_left _ hd0]
        · intro h
          rw [h, Nat.mul_div_cancel' hdvd]
      simp only [hiff]
    · rw [if_neg hdvd]
      refine Finset.sum_eq_zero fun J _ => ?_
      rw [if_neg fun h => hdvd ⟨absNorm J, h.symm⟩]
  have h1 : (∑ I ∈ idealsOfNorm K n, heckeValue 𝔪 ψ I) * (Real.log n : ℂ) =
      ∑ pk ∈ primePowersLe K n, (Real.log (absNorm pk.1) : ℂ) *
        (heckeValue 𝔪 ψ pk.1 ^ pk.2 *
          (if absNorm pk.1 ^ pk.2 ∣ n then heckeCoeff 𝔪 ψ (n / absNorm pk.1 ^ pk.2) else 0)) :=
    (sum_idealsOfNorm_mul_log (heckeValue 𝔪 ψ) hn).trans
      (Finset.sum_congr rfl fun pk hpk => by rw [hinner pk hpk])
  -- the convolution, grouped by the prime powers
  have h2 : ∑ p ∈ n.divisorsAntidiagonal, heckeMangoldt 𝔪 ψ p.1 * heckeCoeff 𝔪 ψ p.2 =
      ∑ pk ∈ primePowersLe K n,
        if absNorm pk.1 ^ pk.2 ∣ n then
          heckeValue 𝔪 ψ pk.1 ^ pk.2 * (Real.log (absNorm pk.1) : ℂ) *
            heckeCoeff 𝔪 ψ (n / absNorm pk.1 ^ pk.2)
        else 0 := by
    rw [Nat.sum_divisorsAntidiagonal (f := fun d e => heckeMangoldt 𝔪 ψ d * heckeCoeff 𝔪 ψ e)]
    have hd : ∀ d ∈ n.divisors, heckeMangoldt 𝔪 ψ d * heckeCoeff 𝔪 ψ (n / d) =
        ∑ pk ∈ primePowersLe K n, if absNorm pk.1 ^ pk.2 = d then
          heckeValue 𝔪 ψ pk.1 ^ pk.2 * (Real.log (absNorm pk.1) : ℂ) * heckeCoeff 𝔪 ψ (n / d)
        else 0 := fun d hd => by
      rw [heckeMangoldt, filter_primePowersLe_eq (Nat.divisor_le hd), Finset.sum_mul,
        Finset.sum_filter]
    rw [Finset.sum_congr rfl hd, Finset.sum_comm]
    refine Finset.sum_congr rfl fun pk _ => ?_
    rw [Finset.sum_ite_eq n.divisors (absNorm pk.1 ^ pk.2) fun d =>
      heckeValue 𝔪 ψ pk.1 ^ pk.2 * (Real.log (absNorm pk.1) : ℂ) * heckeCoeff 𝔪 ψ (n / d)]
    simp only [Nat.mem_divisors, hn0, ne_eq, not_false_eq_true, and_true]
  rw [h2, mul_comm, heckeCoeff, h1]
  refine Finset.sum_congr rfl fun pk _ => ?_
  split_ifs
  · ring
  · ring

/-! ### The size of the coefficients -/

/-- **`|Λ_ψ(n)| ≤ log n · #{𝔞 : N𝔞 = n}`.** -/
theorem norm_heckeMangoldt_le (ψ : HeckeCharacter 𝔪) (n : ℕ) :
    ‖heckeMangoldt 𝔪 ψ n‖ ≤ Real.log n * (idealsOfNorm K n).card := by
  have hcard : ((primePowersLe K n).filter (fun pk => absNorm pk.1 ^ pk.2 = n)).card ≤
      (idealsOfNorm K n).card := by
    refine Finset.card_le_card_of_injOn (fun pk => pk.1 ^ pk.2) ?_ ?_
    · rintro ⟨P, k⟩ hpk
      have h := (Finset.mem_filter.mp (Finset.mem_coe.mp hpk)).2
      exact Finset.mem_coe.mpr (mem_idealsOfNorm.mpr (by rw [map_pow]; exact h))
    · rintro ⟨P, k⟩ hpk ⟨P', k'⟩ hpk' heq
      obtain ⟨h1, hn1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hpk)
      obtain ⟨h2, hn2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hpk')
      obtain ⟨hP, hP0, hk, -⟩ := mem_primePowersLe.mp h1
      obtain ⟨hP', hP0', hk', -⟩ := mem_primePowersLe.mp h2
      dsimp only at heq hn1 hn2
      have hle : P' ^ k' ≤ P := by
        rw [← heq]
        exact Ideal.pow_le_self (by omega)
      haveI := hP
      obtain rfl : P' = P :=
        (hP'.isMaximal hP0').eq_of_le hP.ne_top (Ideal.IsPrime.le_of_pow_le hle)
      have h2' := two_le_absNorm_of_isPrime hP' hP0'
      have hkk : k = k' := Nat.pow_right_injective h2' (hn1.trans hn2.symm)
      rw [hkk]
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  calc ‖heckeMangoldt 𝔪 ψ n‖
      ≤ ∑ pk ∈ (primePowersLe K n).filter (fun pk => absNorm pk.1 ^ pk.2 = n),
          ‖heckeValue 𝔪 ψ pk.1 ^ pk.2 * (Real.log (absNorm pk.1) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _pk ∈ (primePowersLe K n).filter (fun pk => absNorm pk.1 ^ pk.2 = n), Real.log n := by
        refine Finset.sum_le_sum fun pk hpk => ?_
        obtain ⟨P, k⟩ := pk
        obtain ⟨h1, hn1⟩ := Finset.mem_filter.mp hpk
        obtain ⟨hP, hP0, hk, -⟩ := mem_primePowersLe.mp h1
        dsimp only at hn1 ⊢
        have h2' := two_le_absNorm_of_isPrime hP hP0
        have hP1 : (1 : ℝ) ≤ absNorm P := by exact_mod_cast (by omega : 1 ≤ absNorm P)
        have hle : (absNorm P : ℝ) ≤ n := by
          have : absNorm P ≤ absNorm P ^ k := Nat.le_self_pow (by omega) _
          exact_mod_cast this.trans_eq hn1
        have hl0 : 0 ≤ Real.log (absNorm P) := Real.log_nonneg hP1
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hl0]
        calc ‖heckeValue 𝔪 ψ P‖ ^ k * Real.log (absNorm P)
            ≤ 1 * Real.log (absNorm P) :=
              mul_le_mul_of_nonneg_right
                (pow_le_one₀ (norm_nonneg _) (norm_heckeValue_le_one 𝔪 ψ P)) hl0
          _ = Real.log (absNorm P) := one_mul _
          _ ≤ Real.log n := Real.log_le_log (by linarith) hle
    _ = ((primePowersLe K n).filter (fun pk => absNorm pk.1 ^ pk.2 = n)).card * Real.log n := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.log n * (idealsOfNorm K n).card := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hlog0

/-! ### Absolute convergence and the logarithmic derivative -/

theorem lSeriesSummable_card_idealsOfNorm {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((idealsOfNorm K n).card : ℂ)) s := by
  obtain ⟨B, -, hB⟩ := exists_idealCount_le_mul (K := K)
  refine LSeriesSummable_of_sum_norm_bigO (r := 1)
    (Asymptotics.IsBigO.of_bound B (Eventually.of_forall fun n => ?_)) zero_le_one hs
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _), Real.rpow_one,
    Real.norm_of_nonneg (Nat.cast_nonneg n)]
  calc ∑ k ∈ Icc 1 n, ‖((idealsOfNorm K k).card : ℂ)‖
      = ∑ k ∈ Icc 1 n, ((idealsOfNorm K k).card : ℝ) :=
        Finset.sum_congr rfl fun k _ => Complex.norm_natCast _
    _ = idealCount K n := sum_card_idealsOfNorm n
    _ ≤ B * n := hB n

/-- **The series of the von Mangoldt coefficients converges absolutely on `Re s > 1`.** -/
theorem lSeriesSummable_heckeMangoldt (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (heckeMangoldt 𝔪 ψ) s := by
  have habs : LSeries.abscissaOfAbsConv (fun n => ((idealsOfNorm K n).card : ℂ)) < s.re :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => lSeriesSummable_card_idealsOfNorm (by simpa using hy)) (by exact_mod_cast hs)
  have hlog := LSeriesSummable_logMul_of_lt_re habs
  refine Summable.of_norm_bounded hlog.norm fun n => LSeries.norm_term_le s ?_
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have e : ‖LSeries.logMul (fun n => ((idealsOfNorm K n).card : ℂ)) n‖ =
      Real.log n * (idealsOfNorm K n).card := by
    show ‖Complex.log n * ((idealsOfNorm K n).card : ℂ)‖ = _
    rw [← Complex.natCast_log, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog0,
      Complex.norm_natCast]
  rw [e]
  exact norm_heckeMangoldt_le 𝔪 ψ n

/-- **The logarithmic derivative of a Hecke L-series.** On `Re s > 1`,
`L'/L(s, ψ) = −Σ_n Λ_ψ(n) n^{−s}`. -/
theorem logDeriv_heckeL (ψ : HeckeCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (heckeL 𝔪 ψ) s = -LSeries (heckeMangoldt 𝔪 ψ) s := by
  have hc := lSeriesSummable_heckeCoeff 𝔪 ψ hs
  have ha := lSeriesSummable_heckeMangoldt 𝔪 ψ hs
  have habs : LSeries.abscissaOfAbsConv (heckeCoeff 𝔪 ψ) < s.re :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => lSeriesSummable_heckeCoeff 𝔪 ψ (by simpa using hy)) (by exact_mod_cast hs)
  have hconv : LSeries.logMul (heckeCoeff 𝔪 ψ) =
      LSeries.convolution (heckeMangoldt 𝔪 ψ) (heckeCoeff 𝔪 ψ) := by
    rw [LSeries.convolution_def]
    funext n
    show Complex.log n * heckeCoeff 𝔪 ψ n = _
    rw [← Complex.natCast_log]
    exact log_mul_heckeCoeff_eq 𝔪 ψ n
  have hL : heckeL 𝔪 ψ = LSeries (heckeCoeff 𝔪 ψ) := rfl
  have hne : LSeries (heckeCoeff 𝔪 ψ) s ≠ 0 := heckeL_ne_zero 𝔪 ψ hs
  rw [hL, logDeriv_apply, LSeries_deriv habs, hconv, LSeries_convolution' ha hc]
  field_simp

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
