import GaloisForLFunctions.RHTower.WeilLagCompressedMultiplierCriterion

/-!
# Toeplitz positivity of a compressed lag

For a sequence `T : ℕ → ℂ` let `T(−k) = conj T(k)`, and call `T` *Toeplitz positive* if every
Hermitian Toeplitz form `Σ_{i,j} a_i conj(a_j) T(i − j)` has nonnegative real part.

**Theorem** (`toeplitzPositive_compressedLag_of_riemannHypothesis`).  If `Re h = 0` on the critical
line and RH holds, the compressed lag `T(n) = Σ_ρ e^{n h(ρ)}/(ρ(1 − ρ))` is Toeplitz positive.
Every weight `1/(ρ(1 − ρ)) = 1/(¼ + γ²)` is positive and every exponent is unimodular, so the form
is `Σ_ρ |Σ_i a_i e^{i h(ρ)}|²/(¼ + γ²)`.

**Theorem** (`riemannHypothesis_of_toeplitzPositive_compressedLag`).  Conversely, for a compressing
multiplier with `Re h > 0` right of the line, Toeplitz positivity forces RH.  The `2 × 2` forms on
`{0, k}` give `|T(k)| ≤ Re T(0)`, so the compressed lag is bounded above.

**Floors** (`riemannHypothesis_of_toeplitzFloor_subexponential`).  It suffices that every form on
indices `≤ N` is at least `−C_ε e^{εN}` times `Σ |a_i|²`: the `2 × 2` forms then give a
subexponential bound for `T(k)`.  Along apertures, the restricted Weil ground-energy floor of the
same strength needs the zeros to approach the line; along the compressed family it does not.

For `H(z) = z/log(2 − z²)` this gives an unconditional criterion: RH holds iff the compressed lag of
`H` is Toeplitz positive (`riemannHypothesis_iff_toeplitzPositive_logCompressedLag`), and iff its
Toeplitz floors are subexponential (`riemannHypothesis_iff_toeplitzFloor_logCompressedLag`).  For a
single-base lag progression, Toeplitz positivity cannot exclude a non-attained top from zero-side
data (`exists_symmetric_lag_configuration_vanishing_samples`); compression removes that gap.
-/

open Complex Filter Topology
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- The Hermitian extension `T(−k) = conj T(k)` of a sequence to the integers. -/
def hermExt (T : ℕ → ℂ) (k : ℤ) : ℂ := if 0 ≤ k then T k.toNat else conj (T (-k).toNat)

/-- **Toeplitz positivity**: every Hermitian Toeplitz form has nonnegative real part. -/
def ToeplitzPositive (T : ℕ → ℂ) : Prop :=
  ∀ (s : Finset ℕ) (a : ℕ → ℂ),
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) * hermExt T ((i : ℤ) - j)).re

theorem hermExt_natCast (T : ℕ → ℂ) (k : ℕ) : hermExt T k = T k := by
  simp [hermExt]

theorem hermExt_neg_natCast (T : ℕ → ℂ) {k : ℕ} (hk : 0 < k) :
    hermExt T (-(k : ℤ)) = conj (T k) := by
  have h : ¬ (0 : ℤ) ≤ -(k : ℤ) := by omega
  unfold hermExt
  rw [if_neg h, neg_neg, Int.toNat_natCast]

/-- For `Re z = 0`, `e^{(i−j)z} = e^{iz} · conj(e^{jz})`. -/
theorem exp_mul_conj_of_re_eq_zero {z : ℂ} (hz : z.re = 0) (i j : ℕ) :
    Complex.exp (((i : ℤ) - j : ℤ) * z) =
      Complex.exp ((i : ℂ) * z) * conj (Complex.exp ((j : ℂ) * z)) := by
  have hconj : conj z = -z := by
    apply Complex.ext <;> simp [hz]
  rw [← Complex.exp_conj, map_mul, Complex.conj_natCast, hconj, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **RH makes every compressed lag Toeplitz positive.** -/
theorem toeplitzPositive_compressedLag_of_riemannHypothesis (hRH : RiemannHypothesis)
    {h : XiZeroCopy → ℂ} (hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 → (h q).re = 0) :
    ToeplitzPositive (compressedLag h) := by
  intro s a
  have hre : ∀ q : XiZeroCopy, (h q).re = 0 := fun q =>
    hline q (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q)
  have hw : ∀ q : XiZeroCopy, lagWeight q = (cosWeight q : ℂ) := fun q =>
    lagWeight_eq_of_riemannHypothesis hRH q
  have hnorm : ∀ (k : ℤ) (q : XiZeroCopy), ‖lagWeight q * Complex.exp ((k : ℂ) * h q)‖ =
      ‖lagWeight q‖ := by
    intro k q
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.mul_re, hre q]
  have hsumk : ∀ k : ℤ, Summable fun q : XiZeroCopy => lagWeight q * Complex.exp ((k : ℂ) * h q) :=
    fun k => summable_norm_lagWeight.of_norm_bounded fun q => (hnorm k q).le
  -- the Hermitian extension is the zero sum at every integer
  have hext : ∀ i j : ℕ, hermExt (compressedLag h) ((i : ℤ) - j) =
      ∑' q : XiZeroCopy, (cosWeight q : ℂ) * (Complex.exp ((i : ℂ) * h q) *
        conj (Complex.exp ((j : ℂ) * h q))) := by
    intro i j
    have hterm : ∀ q, (cosWeight q : ℂ) * (Complex.exp ((i : ℂ) * h q) *
        conj (Complex.exp ((j : ℂ) * h q))) =
        lagWeight q * Complex.exp ((((i : ℤ) - j : ℤ) : ℂ) * h q) := by
      intro q; rw [hw q, exp_mul_conj_of_re_eq_zero (hre q) i j]
    rw [tsum_congr hterm]
    rcases lt_or_ge (i : ℤ) j with hij | hji
    · obtain ⟨m, hm, hm0⟩ : ∃ m : ℕ, (i : ℤ) - j = -(m : ℤ) ∧ 0 < m :=
        ⟨((j : ℤ) - i).toNat, by omega, by omega⟩
      rw [hm, hermExt_neg_natCast _ hm0, compressedLag, Complex.conj_tsum]
      refine tsum_congr fun q => ?_
      rw [map_mul, hw q, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_natCast]
      have hconj : conj (h q) = -h q := by apply Complex.ext <;> simp [hre q]
      rw [hconj]
      push_cast
      ring_nf
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, (i : ℤ) - j = m := ⟨((i : ℤ) - j).toNat, by omega⟩
      rw [hm, hermExt_natCast, compressedLag]
      rfl
  -- the form is a sum of squares
  have hsummable : ∀ i j : ℕ, Summable fun q : XiZeroCopy => a i * conj (a j) *
      ((cosWeight q : ℂ) * (Complex.exp ((i : ℂ) * h q) *
        conj (Complex.exp ((j : ℂ) * h q)))) := by
    intro i j
    refine ((hsumk ((i : ℤ) - j)).mul_left (a i * conj (a j))).congr fun q => ?_
    rw [hw q, exp_mul_conj_of_re_eq_zero (hre q) i j]
  have hsq : ∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) * hermExt (compressedLag h) ((i : ℤ) - j) =
      ∑' q : XiZeroCopy, (cosWeight q : ℂ) *
        ((∑ i ∈ s, a i * Complex.exp ((i : ℂ) * h q)) *
          conj (∑ j ∈ s, a j * Complex.exp ((j : ℂ) * h q))) := by
    have h1 : ∀ i j : ℕ, a i * conj (a j) * hermExt (compressedLag h) ((i : ℤ) - j) =
        ∑' q : XiZeroCopy, a i * conj (a j) * ((cosWeight q : ℂ) *
          (Complex.exp ((i : ℂ) * h q) * conj (Complex.exp ((j : ℂ) * h q)))) := by
      intro i j; rw [hext, tsum_mul_left]
    simp_rw [h1]
    have h2 : ∀ i : ℕ, ∑ j ∈ s, ∑' q : XiZeroCopy, a i * conj (a j) * ((cosWeight q : ℂ) *
          (Complex.exp ((i : ℂ) * h q) * conj (Complex.exp ((j : ℂ) * h q)))) =
        ∑' q : XiZeroCopy, ∑ j ∈ s, a i * conj (a j) * ((cosWeight q : ℂ) *
          (Complex.exp ((i : ℂ) * h q) * conj (Complex.exp ((j : ℂ) * h q)))) := fun i =>
      (Summable.tsum_finsetSum fun j _ => hsummable i j).symm
    simp_rw [h2]
    rw [← Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hsummable i j]
    refine tsum_congr fun q => ?_
    rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  rw [hsq, Complex.re_tsum]
  · refine tsum_nonneg fun q => ?_
    rw [Complex.mul_conj, Complex.re_ofReal_mul, Complex.ofReal_re]
    exact mul_nonneg (cosWeight_pos q).le (Complex.normSq_nonneg _)
  · have hb : ∀ q : XiZeroCopy, ‖(cosWeight q : ℂ) * ((∑ i ∈ s, a i * Complex.exp ((i : ℂ) * h q)) *
        conj (∑ j ∈ s, a j * Complex.exp ((j : ℂ) * h q)))‖ ≤
        ‖lagWeight q‖ * (∑ i ∈ s, ‖a i‖) ^ 2 := by
      intro q
      have he : ∀ i : ℕ, ‖Complex.exp ((i : ℂ) * h q)‖ = 1 := by
        intro i; rw [Complex.norm_exp]; simp [Complex.mul_re, hre q]
      have hS : ‖∑ i ∈ s, a i * Complex.exp ((i : ℂ) * h q)‖ ≤ ∑ i ∈ s, ‖a i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
        rw [norm_mul, he i, mul_one]
      rw [norm_mul, norm_mul, Complex.norm_conj, ← hw q, sq]
      gcongr
    exact (summable_norm_lagWeight.mul_right _).of_norm_bounded hb

/-- **The `2 × 2` forms on `{0, k}` bound `|T(k)|`.**  If every Hermitian form on `{0, k}`,
`k ≥ 1`, has real part at least `μ (|a₀|² + |a_k|²)`, then `|T(k)| ≤ Re T(0) − μ`. -/
theorem norm_le_of_pair_form {T : ℕ → ℂ} {k : ℕ} (hk : 0 < k) {μ : ℝ}
    (hform : ∀ a : ℕ → ℂ, μ * (‖a 0‖ ^ 2 + ‖a k‖ ^ 2) ≤
      (∑ i ∈ ({0, k} : Finset ℕ), ∑ j ∈ ({0, k} : Finset ℕ),
        a i * conj (a j) * hermExt T ((i : ℤ) - j)).re) :
    ‖T k‖ ≤ (T 0).re - μ := by
  classical
  have hnk : (0 : ℕ) ≠ k := by omega
  have hk0 : (k : ℕ) ≠ 0 := by omega
  have e1 : hermExt T ((0 : ℕ) - (0 : ℕ) : ℤ) = T 0 := by simp [hermExt]
  have e2 : hermExt T ((0 : ℕ) - (k : ℕ) : ℤ) = conj (T k) := by
    rw [show ((0 : ℕ) : ℤ) - (k : ℕ) = -(k : ℤ) by simp, hermExt_neg_natCast _ hk]
  have e3 : hermExt T ((k : ℕ) - (0 : ℕ) : ℤ) = T k := by
    rw [show ((k : ℕ) : ℤ) - (0 : ℕ) = (k : ℤ) by simp, hermExt_natCast]
  have e4 : hermExt T ((k : ℕ) - (k : ℕ) : ℤ) = T 0 := by simp [hermExt]
  by_cases hTk : T k = 0
  · set a : ℕ → ℂ := fun i => if i = 0 then 1 else 0 with ha
    have ha0 : a 0 = 1 := by simp [ha]
    have hak : a k = 0 := by simp [ha, hk0]
    have h := hform a
    rw [Finset.sum_pair hnk, Finset.sum_pair hnk, Finset.sum_pair hnk, ha0, hak, e1] at h
    rw [hTk, norm_zero]
    simp at h
    linarith
  have hnormT : (0 : ℝ) < ‖T k‖ := norm_pos_iff.mpr hTk
  have hnT : (‖T k‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnormT.ne'
  set u : ℂ := -(conj (T k) / (‖T k‖ : ℂ)) with hu
  set a : ℕ → ℂ := fun i => if i = 0 then 1 else u with ha
  have ha0 : a 0 = 1 := by simp [ha]
  have hak : a k = u := by simp [ha, hk0]
  have h := hform a
  rw [Finset.sum_pair hnk, Finset.sum_pair hnk, Finset.sum_pair hnk, ha0, hak] at h
  rw [e1, e2, e3, e4] at h
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_neg, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hnormT, div_self hnormT.ne']
  have hnormu : u * conj u = 1 := by
    rw [Complex.mul_conj', hun]; norm_num
  have huT : u * T k = -(‖T k‖ : ℂ) := by
    rw [hu, neg_mul, div_mul_eq_mul_div, Complex.conj_mul']
    field_simp
  have hc : conj u * conj (T k) = conj (u * T k) := by rw [map_mul]
  have hsum : (1 * conj 1 * T 0 + 1 * conj u * conj (T k) +
      (u * conj 1 * T k + u * conj u * T 0)).re = 2 * (T 0).re - 2 * ‖T k‖ := by
    have e : (1 : ℂ) * conj 1 * T 0 + 1 * conj u * conj (T k) +
        (u * conj 1 * T k + u * conj u * T 0) =
        T 0 + conj (u * T k) + u * T k + u * conj u * T 0 := by
      rw [map_one, ← hc]; ring
    rw [e, huT, hnormu]
    simp
    ring
  rw [hsum, norm_one, hun] at h
  linarith

/-- **Toeplitz positivity forces RH for compressing multipliers.** -/
theorem riemannHypothesis_of_toeplitzPositive_compressedLag {h : XiZeroCopy → ℂ}
    (hc : IsCompressingMultiplier h)
    (hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 → (h q).re ≤ 0)
    (hright : ∀ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re → 0 < (h q).re)
    (hT : ToeplitzPositive (compressedLag h)) : RiemannHypothesis := by
  refine (riemannHypothesis_iff_bddAbove_compressedLag hc hline hright).mpr
    ⟨(compressedLag h 0).re, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact le_rfl
  have hn := norm_le_of_pair_form (T := compressedLag h) hk (μ := 0)
    (fun a => by rw [zero_mul]; exact hT _ a)
  have := Complex.re_le_norm (compressedLag h k)
  linarith

/-- **Toeplitz floors.**  Every Hermitian form of `T` on a finite set of indices `≤ N` has real
part at least `μ Σ |a_i|²`. -/
def ToeplitzFloor (T : ℕ → ℂ) (N : ℕ) (μ : ℝ) : Prop :=
  ∀ (s : Finset ℕ), (∀ i ∈ s, i ≤ N) → ∀ a : ℕ → ℂ,
    μ * ∑ i ∈ s, ‖a i‖ ^ 2 ≤ (∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) * hermExt T ((i : ℤ) - j)).re

/-- **A subexponential Toeplitz floor forces RH for compressing multipliers.**  The analogue for the
restricted Weil ground energy along apertures needs the zeros to approach the line; after
compression no such condition is needed. -/
theorem riemannHypothesis_of_toeplitzFloor_subexponential {h : XiZeroCopy → ℂ}
    (hc : IsCompressingMultiplier h)
    (hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 → (h q).re ≤ 0)
    (hright : ∀ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re → 0 < (h q).re)
    (hfloor : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ToeplitzFloor (compressedLag h) N (-(C * Real.exp (ε * N)))) : RiemannHypothesis := by
  classical
  refine (riemannHypothesis_iff_compressedLag_subexponential hc hline hright).mpr
    fun ε hε => ?_
  obtain ⟨C, hC, hfl⟩ := hfloor ε hε
  refine ⟨|(compressedLag h 0).re| + C, fun k => ?_⟩
  have hE : 1 ≤ Real.exp (ε * k) := Real.one_le_exp (by positivity)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    linarith [le_abs_self (compressedLag h 0).re]
  have hn := norm_le_of_pair_form (T := compressedLag h) hk (μ := -(C * Real.exp (ε * k)))
    (fun a => by
      have := hfl k {0, k} (by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Nat.zero_le _
        · rw [Finset.mem_singleton.mp hi])
        a
      have hnk : (0 : ℕ) ≠ k := by omega
      rwa [Finset.sum_pair hnk] at this)
  have hre := Complex.re_le_norm (compressedLag h k)
  have h0 := le_abs_self (compressedLag h 0).re
  have h1 : |(compressedLag h 0).re| ≤ |(compressedLag h 0).re| * Real.exp (ε * k) :=
    le_mul_of_one_le_right (abs_nonneg _) hE
  nlinarith

/-- Toeplitz positivity is a zero Toeplitz floor. -/
theorem toeplitzFloor_zero_of_toeplitzPositive {T : ℕ → ℂ} (hT : ToeplitzPositive T) (N : ℕ) :
    ToeplitzFloor T N 0 := fun s _ a => by rw [zero_mul]; exact hT s a

/-- The log-compressed multiplier has real part zero on the critical line. -/
theorem re_logCompressedZeroMultiplier_eq_zero {q : XiZeroCopy} (hq : (q.1 : ℂ).re = 1 / 2) :
    (logCompressedZeroMultiplier q).re = 0 :=
  le_antisymm (re_logCompressedZeroMultiplier_nonpos hq.le)
    (by
      have h := re_logCompressedMultiplier_nonpos (z := -(((q.1 : ℂ) - 1 / 2)))
        (by simp [hq]) (by simp [hq])
      have hodd : logCompressedMultiplier (-(((q.1 : ℂ) - 1 / 2))) =
          -logCompressedMultiplier ((q.1 : ℂ) - 1 / 2) := by
        unfold logCompressedMultiplier
        rw [neg_sq, neg_div]
      rw [hodd, Complex.neg_re] at h
      exact neg_nonpos.mp h)

/-- **RH ⟺ Toeplitz positivity of the logarithmically compressed lag.** -/
theorem riemannHypothesis_iff_toeplitzPositive_logCompressedLag :
    RiemannHypothesis ↔ ToeplitzPositive (compressedLag logCompressedZeroMultiplier) :=
  ⟨fun hRH => toeplitzPositive_compressedLag_of_riemannHypothesis hRH
      fun _ hq => re_logCompressedZeroMultiplier_eq_zero hq,
    riemannHypothesis_of_toeplitzPositive_compressedLag
      isCompressingMultiplier_logCompressedZeroMultiplier
      (fun _ hq => re_logCompressedZeroMultiplier_nonpos hq.le)
      (fun _ hq => re_logCompressedZeroMultiplier_pos hq)⟩

/-- **RH ⟺ subexponential Toeplitz floors of the logarithmically compressed lag.** -/
theorem riemannHypothesis_iff_toeplitzFloor_logCompressedLag :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ToeplitzFloor (compressedLag logCompressedZeroMultiplier) N (-(C * Real.exp (ε * N))) := by
  constructor
  · intro hRH ε _
    refine ⟨0, le_rfl, fun N => ?_⟩
    simpa using toeplitzFloor_zero_of_toeplitzPositive
      (riemannHypothesis_iff_toeplitzPositive_logCompressedLag.mp hRH) N
  · exact riemannHypothesis_of_toeplitzFloor_subexponential
      isCompressingMultiplier_logCompressedZeroMultiplier
      (fun _ hq => re_logCompressedZeroMultiplier_nonpos hq.le)
      (fun _ hq => re_logCompressedZeroMultiplier_pos hq)

end

end RHTower
