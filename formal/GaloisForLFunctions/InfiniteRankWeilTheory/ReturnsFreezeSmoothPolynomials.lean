import Mathlib

/-!
# Returns freeze smooth Dirichlet polynomials: the archimedean Frobenius substitute

Over `𝔽_q` Stepanov's method rests on one identity: `x^q − x` vanishes at every point, so an auxiliary
polynomial built from `x` and `x^q` vanishes to high order at all points at low degree. Over `ℤ` the
"points" at height `t` are the phases `n^{−it}`, and a **return** is a height at which every prime
phase up to `y` is within `δ` of `1`.

* `norm_phase_sub_one_le_of_smooth`: at a `δ`-return of a set of primes `P`, every `P`-smooth integer
  `n` has `|n^{−it} − 1| ≤ Ω(n) δ`.
* `norm_dpoly_shift_sub_le`: hence a Dirichlet polynomial supported on `P`-smooth integers moves by at
  most `δ Σ |c_n n^{−s}| Ω(n)` when `s` is shifted by a return: **returns freeze smooth polynomials**,
  together with all their derivatives (apply it to the coefficients `c_n (−log n)^j`).
* `exists_ne_zero_moments_eq_zero`: on any `J + 1` integers there is a nonzero polynomial whose first
  `J` logarithmic moments at `s₀` vanish, i.e. with a zero of order `J` at `s₀`.
* `norm_dpoly_le_expTail`: such a polynomial is flat near `s₀`: `|A(s₀ + w)|` is at most the `J`-th
  exponential tail `Σ_n |c_n n^{−s₀}| (e^{|w| log n} − Σ_{j<J} (|w| log n)^j/j!)`.
* `norm_dpoly_near_return_le`: **forced vanishing at every return.** At every `δ`-return `t`, the
  polynomial is at most `δ·(mass) + (J-th tail)` on the whole disc about `s₀ + it`. Moment conditions
  are the archimedean shadow of `x^q − x`: `J` linear conditions force approximate vanishing to order
  `J` at all returns simultaneously.
* `eq_zero_of_exact_return`: but there are no exact returns: for two distinct primes, `p^{it} = 1` and
  `q^{it} = 1` force `t = 0`. Over `𝔽_q` every point is fixed by a power of Frobenius; the prime orbit
  of `ℤ` has a single fixed point. Forced vanishing is therefore approximate only, and the copy of a
  zero of order `J` at a return needs the precision `δ` to beat the `J`-th exponential tail.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The phase `n^{−it} = e^{−it log n}`. -/
def phase (n : ℕ) (t : ℝ) : ℂ := Complex.exp (((-(t * Real.log n) : ℝ) : ℂ) * I)

theorem norm_phase (n : ℕ) (t : ℝ) : ‖phase n t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem complex_log_natCast (n : ℕ) : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
  rw [Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast]

theorem phase_one (t : ℝ) : phase 1 t = 1 := by simp [phase]

theorem phase_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (t : ℝ) :
    phase (m * n) t = phase m t * phase n t := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)]
  push_cast
  ring

theorem norm_mul_sub_one_le {u v : ℂ} (hu : ‖u‖ = 1) : ‖u * v - 1‖ ≤ ‖u - 1‖ + ‖v - 1‖ := by
  calc ‖u * v - 1‖ = ‖u * (v - 1) + (u - 1)‖ := by ring_nf
    _ ≤ ‖u * (v - 1)‖ + ‖u - 1‖ := norm_add_le _ _
    _ = ‖v - 1‖ + ‖u - 1‖ := by rw [norm_mul, hu, one_mul]
    _ = ‖u - 1‖ + ‖v - 1‖ := add_comm _ _

/-- A height `t` is a **`δ`-return** of a set of primes `P` if every phase `p^{−it}`, `p ∈ P`, is within
`δ` of `1`. -/
def IsReturn (P : Finset ℕ) (δ t : ℝ) : Prop := ∀ p ∈ P, ‖phase p t - 1‖ ≤ δ

/-- Products of returning phases return, with the errors adding up. -/
theorem norm_phase_prod_sub_one_le {P : Finset ℕ} {δ t : ℝ} (ht : IsReturn P δ t) :
    ∀ L : List ℕ, (∀ p ∈ L, p ∈ P ∧ p ≠ 0) → ‖phase L.prod t - 1‖ ≤ L.length * δ
  | [], _ => by simp [phase_one]
  | p :: L, hL => by
    have hp := hL p (List.mem_cons_self ..)
    have hL' : ∀ q ∈ L, q ∈ P ∧ q ≠ 0 := fun q hq => hL q (List.mem_cons_of_mem _ hq)
    have hprod : L.prod ≠ 0 := List.prod_ne_zero fun h => (hL' 0 h).2 rfl
    rw [List.prod_cons, phase_mul hp.2 hprod]
    refine (norm_mul_sub_one_le (norm_phase _ _)).trans ?_
    have := norm_phase_prod_sub_one_le ht L hL'
    rw [List.length_cons]
    push_cast
    linarith [ht p hp.1]

/-- **Smooth integers return.** At a `δ`-return of `P`, a `P`-smooth `n ≥ 1` has
`|n^{−it} − 1| ≤ Ω(n) δ`. -/
theorem norm_phase_sub_one_le_of_smooth {P : Finset ℕ} {δ t : ℝ} (ht : IsReturn P δ t) {n : ℕ}
    (hn : n ≠ 0) (hsmooth : ∀ p ∈ n.primeFactorsList, p ∈ P) :
    ‖phase n t - 1‖ ≤ n.primeFactorsList.length * δ := by
  have h := norm_phase_prod_sub_one_le ht n.primeFactorsList fun p hp =>
    ⟨hsmooth p hp, (Nat.prime_of_mem_primeFactorsList hp).ne_zero⟩
  rwa [Nat.prod_primeFactorsList hn] at h

/-- The Dirichlet polynomial `A(s) = Σ_{n∈S} c_n n^{−s}`. -/
def dpoly (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ := ∑ n ∈ S, c n * (n : ℂ) ^ (-s)

theorem natCast_cpow_shift {n : ℕ} (hn : n ≠ 0) (s : ℂ) (t : ℝ) :
    (n : ℂ) ^ (-(s + t * I)) = (n : ℂ) ^ (-s) * phase n t := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have h : (n : ℂ) ^ (-((t : ℂ) * I)) = phase n t := by
    rw [Complex.cpow_def_of_ne_zero hn', complex_log_natCast, phase]
    congr 1
    push_cast
    ring
  rw [neg_add, Complex.cpow_add _ _ hn', h]

/-- **Returns freeze smooth polynomials.** For `S` of `P`-smooth positive integers and a `δ`-return
`t`, `|A(s + it) − A(s)| ≤ δ Σ_{n∈S} |c_n n^{−s}| Ω(n)`. -/
theorem norm_dpoly_shift_sub_le {P : Finset ℕ} {δ t : ℝ} (ht : IsReturn P δ t) {S : Finset ℕ}
    (hS0 : ∀ n ∈ S, n ≠ 0) (hS : ∀ n ∈ S, ∀ p ∈ n.primeFactorsList, p ∈ P) (c : ℕ → ℂ)
    (s : ℂ) :
    ‖dpoly S c (s + t * I) - dpoly S c s‖ ≤
      δ * ∑ n ∈ S, ‖c n * (n : ℂ) ^ (-s)‖ * n.primeFactorsList.length := by
  unfold dpoly
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [natCast_cpow_shift (hS0 n hn), show c n * ((n : ℂ) ^ (-s) * phase n t) -
    c n * (n : ℂ) ^ (-s) = c n * (n : ℂ) ^ (-s) * (phase n t - 1) by ring, norm_mul]
  have := norm_phase_sub_one_le_of_smooth ht (hS0 n hn) (hS n hn)
  nlinarith [norm_nonneg (c n * (n : ℂ) ^ (-s))]

/-! ### Moment-annihilated polynomials -/

/-- The `j`-th logarithmic moment `Σ_n c_n n^{−s₀} (−log n)^j`, the `j`-th derivative at `s₀`. -/
def logMoment (S : Finset ℕ) (c : ℕ → ℂ) (s₀ : ℂ) (j : ℕ) : ℂ :=
  ∑ n ∈ S, c n * (n : ℂ) ^ (-s₀) * (-(Real.log n : ℂ)) ^ j

/-- The moment map `c ↦ (Σ_n c_n n^{−s₀} (−log n)^j)_{j<J}` on coefficient vectors over `S`. -/
def momentMap (S : Finset ℕ) (s₀ : ℂ) (J : ℕ) : (S → ℂ) →ₗ[ℂ] (Fin J → ℂ) where
  toFun x j := ∑ n : S, x n * ((n : ℕ) : ℂ) ^ (-s₀) * (-((Real.log (n : ℕ) : ℝ) : ℂ)) ^ (j : ℕ)
  map_add' x y := by
    ext j; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem momentMap_apply (S : Finset ℕ) (s₀ : ℂ) (J : ℕ) (x : S → ℂ) (j : Fin J) :
    momentMap S s₀ J x j =
      ∑ n : S, x n * ((n : ℕ) : ℂ) ^ (-s₀) * (-((Real.log (n : ℕ) : ℝ) : ℂ)) ^ (j : ℕ) := rfl

/-- **Existence.** On any set of more than `J` integers there is a nonzero coefficient vector whose
first `J` logarithmic moments at `s₀` vanish. -/
theorem exists_ne_zero_moments_eq_zero (S : Finset ℕ) {J : ℕ} (hJ : J < S.card) (s₀ : ℂ) :
    ∃ c : ℕ → ℂ, (∃ n ∈ S, c n ≠ 0) ∧ (∀ n ∉ S, c n = 0) ∧
      ∀ j < J, logMoment S c s₀ j = 0 := by
  classical
  have hrank : Module.finrank ℂ (Fin J → ℂ) < Module.finrank ℂ (S → ℂ) := by
    simpa [Module.finrank_fintype_fun_eq_card] using hJ
  obtain ⟨x, hxker, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := momentMap S s₀ J) hrank)
  refine ⟨fun n => if h : n ∈ S then x ⟨n, h⟩ else 0, ?_, fun n hn => by simp [hn], fun j hj => ?_⟩
  · by_contra hall
    push Not at hall
    exact hx0 (funext fun n => by simpa [n.2] using hall n n.2)
  · have h0 := congrFun (LinearMap.mem_ker.mp hxker) ⟨j, hj⟩
    rw [momentMap_apply, Pi.zero_apply] at h0
    rw [logMoment, ← h0, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [n.2]

/-- **Flatness at a zero of order `J`.** If the first `J` logarithmic moments at `s₀` vanish,
`|A(s₀ + w)|` is at most the `J`-th exponential tail. -/
theorem norm_dpoly_le_expTail {S : Finset ℕ} (hS0 : ∀ n ∈ S, n ≠ 0) {c : ℕ → ℂ} {s₀ : ℂ} {J : ℕ}
    (hmom : ∀ j < J, logMoment S c s₀ j = 0) (w : ℂ) :
    ‖dpoly S c (s₀ + w)‖ ≤ ∑ n ∈ S, ‖c n * (n : ℂ) ^ (-s₀)‖ *
      (Real.exp (‖w‖ * Real.log n) -
        ∑ j ∈ range J, (‖w‖ * Real.log n) ^ j / (j.factorial : ℝ)) := by
  have hexp : ∀ n ∈ S, (n : ℂ) ^ (-(s₀ + w)) = (n : ℂ) ^ (-s₀) * Complex.exp (-w * Real.log n) := by
    intro n hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hS0 n hn
    have h : (n : ℂ) ^ (-w) = Complex.exp (-w * Real.log n) := by
      rw [Complex.cpow_def_of_ne_zero hn', complex_log_natCast]
      ring_nf
    rw [neg_add, Complex.cpow_add _ _ hn', h]
  have hzero : ∑ n ∈ S, c n * (n : ℂ) ^ (-s₀) *
      ∑ j ∈ range J, (-w * Real.log n) ^ j / (j.factorial : ℂ) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hm := hmom j (Finset.mem_range.1 hj)
    unfold logMoment at hm
    have : ∑ n ∈ S, c n * (n : ℂ) ^ (-s₀) * ((-w * Real.log n) ^ j / (j.factorial : ℂ)) =
        (w ^ j / (j.factorial : ℂ)) *
          ∑ n ∈ S, c n * (n : ℂ) ^ (-s₀) * (-(Real.log n : ℂ)) ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [mul_pow, neg_pow, neg_pow]
      ring
    rw [this, hm, mul_zero]
  have hrepr : dpoly S c (s₀ + w) = ∑ n ∈ S, c n * (n : ℂ) ^ (-s₀) *
      (Complex.exp (-w * Real.log n) -
        ∑ j ∈ range J, (-w * Real.log n) ^ j / (j.factorial : ℂ)) := by
    unfold dpoly
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [hzero, sub_zero]
    exact Finset.sum_congr rfl fun n hn => by rw [hexp n hn, mul_assoc]
  rw [hrepr]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hnorm : ‖-w * (Real.log n : ℂ)‖ = ‖w‖ * Real.log n := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hlog]
  have := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum (-w * Real.log n) J
  rwa [hnorm] at this

/-- **Forced vanishing at every return.** For a polynomial on `P`-smooth integers whose first `J`
logarithmic moments at `s₀` vanish, at every `δ`-return `t` and every `w`:
`|A(s₀ + w + it)| ≤ δ Σ|c_n n^{−(s₀+w)}| Ω(n) + (J-th exponential tail at |w|)`. -/
theorem norm_dpoly_near_return_le {P : Finset ℕ} {δ t : ℝ} (ht : IsReturn P δ t) {S : Finset ℕ}
    (hS0 : ∀ n ∈ S, n ≠ 0) (hS : ∀ n ∈ S, ∀ p ∈ n.primeFactorsList, p ∈ P) {c : ℕ → ℂ}
    {s₀ : ℂ} {J : ℕ} (hmom : ∀ j < J, logMoment S c s₀ j = 0) (w : ℂ) :
    ‖dpoly S c (s₀ + w + t * I)‖ ≤
      δ * ∑ n ∈ S, ‖c n * (n : ℂ) ^ (-(s₀ + w))‖ * n.primeFactorsList.length +
        ∑ n ∈ S, ‖c n * (n : ℂ) ^ (-s₀)‖ *
          (Real.exp (‖w‖ * Real.log n) -
            ∑ j ∈ range J, (‖w‖ * Real.log n) ^ j / (j.factorial : ℝ)) := by
  have h1 := norm_dpoly_shift_sub_le ht hS0 hS c (s₀ + w)
  have h2 := norm_dpoly_le_expTail hS0 hmom w
  calc ‖dpoly S c (s₀ + w + t * I)‖
      = ‖(dpoly S c (s₀ + w + t * I) - dpoly S c (s₀ + w)) + dpoly S c (s₀ + w)‖ := by ring_nf
    _ ≤ ‖dpoly S c (s₀ + w + t * I) - dpoly S c (s₀ + w)‖ + ‖dpoly S c (s₀ + w)‖ :=
        norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2

/-! ### No exact returns -/

/-- **The prime orbit has one fixed point.** For distinct primes `p, q`, `p^{−it} = q^{−it} = 1`
forces `t = 0`. -/
theorem eq_zero_of_exact_return {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {t : ℝ}
    (htp : phase p t = 1) (htq : phase q t = 1) : t = 0 := by
  by_contra ht0
  rw [phase, Complex.exp_eq_one_iff] at htp htq
  obtain ⟨a, ha⟩ := htp
  obtain ⟨b, hb⟩ := htq
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- compare: `−t log p = 2πa`, `−t log q = 2πb`
  have ha' : -(t * Real.log p) = a * (2 * Real.pi) := by
    have h1 : ((-(t * Real.log p) : ℝ) : ℂ) * I = ((a * (2 * Real.pi) : ℝ) : ℂ) * I := by
      rw [ha]; push_cast; ring
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h1
  have hb' : -(t * Real.log q) = b * (2 * Real.pi) := by
    have h1 : ((-(t * Real.log q) : ℝ) : ℂ) * I = ((b * (2 * Real.pi) : ℝ) : ℂ) * I := by
      rw [hb]; push_cast; ring
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h1
  have hrel : (b : ℝ) * Real.log p = a * Real.log q := by
    have h1 : (b : ℝ) * (a * (2 * Real.pi)) = a * (b * (2 * Real.pi)) := by ring
    rw [← ha', ← hb'] at h1
    have : t * ((b : ℝ) * Real.log p - a * Real.log q) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h ht0
    · linarith
  have ha0 : a ≠ 0 := by
    rintro rfl
    have : t * Real.log p = 0 := by
      simp only [Int.cast_zero, zero_mul] at ha'; linarith
    rcases mul_eq_zero.1 this with h | h
    · exact ht0 h
    · exact hlp.ne' h
  -- both coefficients have the same sign; normalize to positive integers
  obtain ⟨a', b', ha'0, hb'0, hrel'⟩ : ∃ a' b' : ℤ, 0 < a' ∧ 0 < b' ∧
      (b' : ℝ) * Real.log p = a' * Real.log q := by
    rcases lt_or_gt_of_ne ha0 with ha1 | ha1
    · have hb1 : b < 0 := by
        by_contra hb1
        push Not at hb1
        have h1 : (0 : ℝ) ≤ b * Real.log p := mul_nonneg (by exact_mod_cast hb1) hlp.le
        have h2 : (a : ℝ) * Real.log q < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast ha1) hlq
        linarith
      exact ⟨-a, -b, by omega, by omega, by push_cast; linarith⟩
    · have hb1 : 0 < b := by
        by_contra hb1
        push Not at hb1
        have h1 : (b : ℝ) * Real.log p ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hb1) hlp.le
        have h2 : 0 < (a : ℝ) * Real.log q := mul_pos (by exact_mod_cast ha1) hlq
        linarith
      exact ⟨a, b, ha1, hb1, hrel⟩
  obtain ⟨m, n, hm, hn, hmn⟩ : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      (m : ℝ) * Real.log p = n * Real.log q := by
    refine ⟨b'.toNat, a'.toNat, by omega, by omega, ?_⟩
    have e1 : ((b'.toNat : ℕ) : ℝ) = (b' : ℝ) := by
      have := Int.toNat_of_nonneg hb'0.le; exact_mod_cast this
    have e2 : ((a'.toNat : ℕ) : ℝ) = (a' : ℝ) := by
      have := Int.toNat_of_nonneg ha'0.le; exact_mod_cast this
    rw [e1, e2]; exact hrel'
  have hpow : (p : ℝ) ^ m = (q : ℝ) ^ n := by
    have := congrArg Real.exp hmn
    rwa [← Real.log_pow, ← Real.log_pow, Real.exp_log (pow_pos (by exact_mod_cast hp.pos) m),
      Real.exp_log (pow_pos (by exact_mod_cast hq.pos) n)] at this
  have hnat : p ^ m = q ^ n := by exact_mod_cast hpow
  have hdvd : p ∣ q ^ n := ⟨p ^ (m - 1), by rw [← hnat, ← pow_succ', Nat.sub_add_cancel hm]⟩
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hdvd))

end GaloisForLFunctions.InfiniteRankWeilTheory
