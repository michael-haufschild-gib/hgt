import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The radial tail carries an exact divisibility module

The radial components of the exterior tail are

```text
H q lam n s = √(lam * exp s) * q (n * (lam * exp s)),
```

and multiplicative translation acts on them by index multiplication.

* `radialComponent_add_log` — the dilation identity: `H n (s + log m) = √m * H (m * n) s`.  So
  translating by `log m` selects exactly the radial indices divisible by `m`.
* `sum_radialComponent_add_log` — the same statement for a truncated sum.
* `moebius_recovery` — finite Möbius inversion: every radial component up to the cutoff is recovered
  from the divisible tails.  The coefficient bookkeeping is `∑_{d ∣ k} μ d = if k = 1 then 1 else 0`,
  and the reindexing is the bijection `(d, r) ↦ (d * r, d)`.
* `eq_zero_of_powerSums_tendsto` — the algebraic core of the exact finite radial dimension.  The card
  proves independence with a generalized Vandermonde determinant and Schur-polynomial positivity;
  this replaces that by an elementary dominant-term limit: if `∑_{n ≤ K} a n * n ^ r i = 0` along any
  exponents `r i → ∞`, then dividing by `K ^ r i` kills every lower node and forces `a K = 0`,
  and descending induction finishes.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology Finset ArithmeticFunction

/-! ## Radial components and the dilation identity -/

/-- The `n`-th radial component of the exterior tail. -/
def radialComponent (q : ℝ → ℂ) (lam : ℝ) (n : ℕ) (s : ℝ) : ℂ :=
  (Real.sqrt (lam * Real.exp s) : ℂ) * q (n * (lam * Real.exp s))

/-- **Equation (4).**  Multiplicative translation by `m` multiplies the radial index by `m`. -/
theorem radialComponent_add_log (q : ℝ → ℂ) {lam : ℝ} (_hlam : 0 ≤ lam) {m : ℕ} (hm : 0 < m)
    (n : ℕ) (s : ℝ) :
    radialComponent q lam n (s + Real.log m) =
      (Real.sqrt m : ℂ) * radialComponent q lam (m * n) s := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hexp : Real.exp (s + Real.log m) = (m : ℝ) * Real.exp s := by
    rw [Real.exp_add, Real.exp_log hmpos, mul_comm]
  have harg : lam * Real.exp (s + Real.log m) = (m : ℝ) * (lam * Real.exp s) := by
    rw [hexp]; ring
  have hsqrt : Real.sqrt (lam * Real.exp (s + Real.log m))
      = Real.sqrt m * Real.sqrt (lam * Real.exp s) := by
    rw [harg, Real.sqrt_mul hmpos.le]
  have h1 : ((Real.sqrt (lam * Real.exp (s + Real.log m)) : ℝ) : ℂ)
      = (Real.sqrt m : ℂ) * (Real.sqrt (lam * Real.exp s) : ℂ) := by
    rw [hsqrt]; push_cast; ring
  have h2 : ((n : ℝ) * (lam * Real.exp (s + Real.log m)))
      = ((m * n : ℕ) : ℝ) * (lam * Real.exp s) := by
    rw [harg]; push_cast; ring
  simp only [radialComponent]
  rw [h1, h2]
  ring

/-- **Equation (5).**  A truncated sum of radial components translates to the sum over the indices
divisible by `m`. -/
theorem sum_radialComponent_add_log (q : ℝ → ℂ) {lam : ℝ} (hlam : 0 ≤ lam) {m : ℕ} (hm : 0 < m)
    (N : ℕ) (s : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, radialComponent q lam n (s + Real.log m))
      = (Real.sqrt m : ℂ) * ∑ n ∈ Finset.Icc 1 N, radialComponent q lam (m * n) s := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => radialComponent_add_log q hlam hm n s

/-! ## The Möbius coefficient identity -/

/-- `∑_{d ∣ k} μ d` is one at `k = 1` and zero otherwise. -/
theorem sum_divisors_moebius (k : ℕ) :
    (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℤ)) = if k = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f k) moebius_mul_coe_zeta
  rw [coe_mul_zeta_apply] at h
  rw [h]
  simp [ArithmeticFunction.one_apply]

/-! ## Finite Möbius recovery -/

/-- The truncated divisible tail at cutoff `K`. -/
def divisibleTail (q : ℝ → ℂ) (lam : ℝ) (K m : ℕ) (s : ℝ) : ℂ :=
  ∑ r ∈ Finset.Icc 1 (K / m), radialComponent q lam (m * r) s

/-- **Equation (7).**  Finite Möbius inversion recovers each radial component from the divisible
tails.  The reindexing is `(d, r) ↦ (d * r, d)`, and the resulting coefficient of the index `n * k` is
`∑_{d ∣ k} μ d`. -/
theorem moebius_recovery (q : ℝ → ℂ) (lam : ℝ) {K n : ℕ} (hn : 0 < n) (hnK : n ≤ K) (s : ℝ) :
    (∑ d ∈ Finset.Icc 1 (K / n), (ArithmeticFunction.moebius d : ℂ) * divisibleTail q lam K (n * d) s)
      = radialComponent q lam n s := by
  classical
  -- expand and reindex the double sum
  have hsig := Finset.sum_sigma' (Finset.Icc 1 (K / n))
    (fun d => Finset.Icc 1 (K / (n * d)))
    (fun d r => (ArithmeticFunction.moebius d : ℂ) * radialComponent q lam (n * d * r) s)
  have hexp : (∑ d ∈ Finset.Icc 1 (K / n), (ArithmeticFunction.moebius d : ℂ) * divisibleTail q lam K (n * d) s)
      = ∑ d ∈ Finset.Icc 1 (K / n), ∑ r ∈ Finset.Icc 1 (K / (n * d)),
          (ArithmeticFunction.moebius d : ℂ) * radialComponent q lam (n * d * r) s :=
    Finset.sum_congr rfl fun d _ => by rw [divisibleTail, Finset.mul_sum]
  -- regroup by the product `k = d * r`
  have hgroup : (∑ x ∈ (Finset.Icc 1 (K / n)).sigma fun d => Finset.Icc 1 (K / (n * d)),
        (ArithmeticFunction.moebius x.1 : ℂ) * radialComponent q lam (n * x.1 * x.2) s)
      = ∑ y ∈ (Finset.Icc 1 (K / n)).sigma fun k => k.divisors,
        (ArithmeticFunction.moebius y.2 : ℂ) * radialComponent q lam (n * y.1) s := by
    refine Finset.sum_nbij' (fun x => ⟨x.1 * x.2, x.1⟩) (fun y => ⟨y.2, y.1 / y.2⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨d, r⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx ⊢
      obtain ⟨⟨hd1, hdK⟩, hr1, hrK⟩ := hx
      have hdpos : 0 < d := hd1
      have hnd : 0 < n * d := Nat.mul_pos hn hdpos
      have hdr : d * r ≤ K / n := by
        rw [Nat.le_div_iff_mul_le hn]
        rw [Nat.le_div_iff_mul_le hnd] at hrK
        calc d * r * n = r * (n * d) := by ring
          _ ≤ K := hrK
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hdr⟩,
        ⟨Dvd.intro r rfl, by positivity⟩⟩
    · rintro ⟨k, d⟩ hy
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hy ⊢
      obtain ⟨⟨hk1, hkK⟩, hdvd, hkne⟩ := hy
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hdk : d ≤ k := Nat.le_of_dvd (by omega) hdvd
      have hnd : 0 < n * d := Nat.mul_pos hn hdpos
      refine ⟨⟨hdpos, le_trans hdk hkK⟩, ?_, ?_⟩
      · exact Nat.one_le_div_iff hdpos |>.mpr hdk
      · rw [Nat.le_div_iff_mul_le hnd]
        have hkn : k * n ≤ K := by
          rw [Nat.le_div_iff_mul_le hn] at hkK
          exact hkK
        calc k / d * (n * d) = n * (d * (k / d)) := by ring
          _ = n * k := by rw [Nat.mul_div_cancel' hdvd]
          _ = k * n := by ring
          _ ≤ K := hkn
    · rintro ⟨d, r⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hx
      have hdpos : 0 < d := hx.1.1
      simp [Nat.mul_div_cancel_left _ hdpos]
    · rintro ⟨k, d⟩ hy
      simp only [Finset.mem_sigma, Nat.mem_divisors] at hy
      obtain ⟨_, hdvd, _⟩ := hy
      simp [Nat.mul_div_cancel' hdvd]
    · rintro ⟨d, r⟩ _
      rw [show n * d * r = n * (d * r) from by ring]
  -- evaluate the inner Möbius sums
  have hinner : (∑ y ∈ (Finset.Icc 1 (K / n)).sigma fun k => k.divisors,
        (ArithmeticFunction.moebius y.2 : ℂ) * radialComponent q lam (n * y.1) s)
      = ∑ k ∈ Finset.Icc 1 (K / n),
        (if k = 1 then (1 : ℂ) else 0) * radialComponent q lam (n * k) s := by
    rw [← Finset.sum_sigma' (Finset.Icc 1 (K / n)) (fun k => k.divisors)
      (fun k d => (ArithmeticFunction.moebius d : ℂ) * radialComponent q lam (n * k) s)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    have := sum_divisors_moebius k
    calc (∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℂ)) = ((∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℤ) : ℤ) : ℂ) := by push_cast; rfl
      _ = ((if k = 1 then (1 : ℤ) else 0 : ℤ) : ℂ) := by rw [this]
      _ = if k = 1 then (1 : ℂ) else 0 := by split_ifs <;> simp
  rw [hexp, hsig, hgroup, hinner]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro k hk hk1
    simp [hk1]
  · intro hk
    exfalso
    refine hk ?_
    simp only [Finset.mem_Icc]
    exact ⟨le_rfl, Nat.one_le_div_iff hn |>.mpr hnK⟩

/-! ## The algebraic core of exact finite radial dimension -/

/-- **The dominant-term independence lemma.**  If a finite combination of the power functions
`n ↦ n ^ r` over the nodes `1, …, K` vanishes along exponents tending to infinity, all coefficients
vanish.  Dividing by `K ^ r` sends every lower node to zero, which forces the top coefficient to
vanish; descending induction finishes.  This replaces the generalized Vandermonde determinant and its
Schur-positivity input. -/
theorem eq_zero_of_powerSums_tendsto {K : ℕ} {a : ℕ → ℂ} {r : ℕ → ℕ}
    (hr : Tendsto r atTop atTop)
    (h : ∀ i, (∑ n ∈ Finset.Icc 1 K, a n * (n : ℂ) ^ (r i)) = 0) :
    ∀ n ∈ Finset.Icc 1 K, a n = 0 := by
  induction K with
  | zero => intro n hn; simp at hn
  | succ K ih =>
    have hKpos : (0 : ℝ) < ((K : ℝ) + 1) := by positivity
    -- the normalized relation
    have hnorm : ∀ i, a (K + 1)
        = -∑ n ∈ Finset.Icc 1 K, a n * ((n : ℂ) / ((K : ℂ) + 1)) ^ (r i) := by
      intro i
      have hsplit : (∑ n ∈ Finset.Icc 1 (K + 1), a n * (n : ℂ) ^ (r i))
          = (∑ n ∈ Finset.Icc 1 K, a n * (n : ℂ) ^ (r i))
            + a (K + 1) * ((K : ℂ) + 1) ^ (r i) := by
        rw [Finset.sum_Icc_succ_top (by omega)]
        push_cast
        ring
      have hne : ((K : ℂ) + 1) ^ (r i) ≠ 0 := by
        refine pow_ne_zero _ ?_
        intro hzero
        have hre := congrArg Complex.re hzero
        simp at hre
        exact absurd hre (by positivity)
      have hz := h i
      rw [hsplit] at hz
      have hsum : (∑ n ∈ Finset.Icc 1 K, a n * ((n : ℂ) / ((K : ℂ) + 1)) ^ (r i))
          = (∑ n ∈ Finset.Icc 1 K, a n * (n : ℂ) ^ (r i)) / ((K : ℂ) + 1) ^ (r i) := by
        rw [eq_div_iff hne, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [div_pow]
        field_simp
      rw [hsum]
      field_simp
      linear_combination hz
    -- the normalized sum tends to zero
    have hlim : Tendsto
        (fun i => -∑ n ∈ Finset.Icc 1 K, a n * ((n : ℂ) / ((K : ℂ) + 1)) ^ (r i))
        atTop (nhds 0) := by
      have hterm : ∀ n ∈ Finset.Icc 1 K,
          Tendsto (fun i => a n * ((n : ℂ) / ((K : ℂ) + 1)) ^ (r i)) atTop (nhds 0) := by
        intro n hn
        simp only [Finset.mem_Icc] at hn
        have hlt : ‖(n : ℂ) / ((K : ℂ) + 1)‖ < 1 := by
          have hnum : ‖(n : ℂ)‖ = (n : ℝ) := by simp
          have hden : ‖((K : ℂ) + 1)‖ = (K : ℝ) + 1 := by
            have : ((K : ℂ) + 1) = ((((K : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
            rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hKpos]
          rw [norm_div, hnum, hden, div_lt_one hKpos]
          have : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast hn.2
          linarith
        have hpow : Tendsto (fun i => ((n : ℂ) / ((K : ℂ) + 1)) ^ (r i)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt).comp hr
        simpa using hpow.const_mul (a n)
      have := tendsto_finsetSum (Finset.Icc 1 K) hterm
      simpa using this.neg
    -- hence the top coefficient vanishes
    have htop : a (K + 1) = 0 := by
      have hconst : Tendsto (fun _ : ℕ => a (K + 1)) atTop (nhds (a (K + 1))) :=
        tendsto_const_nhds
      have heq : (fun i : ℕ => a (K + 1))
          = fun i => -∑ n ∈ Finset.Icc 1 K, a n * ((n : ℂ) / ((K : ℂ) + 1)) ^ (r i) :=
        funext hnorm
      rw [heq] at hconst
      exact tendsto_nhds_unique hconst hlim
    -- and the remaining relation is the inductive hypothesis
    have hrest : ∀ i, (∑ n ∈ Finset.Icc 1 K, a n * (n : ℂ) ^ (r i)) = 0 := by
      intro i
      have hsplit : (∑ n ∈ Finset.Icc 1 (K + 1), a n * (n : ℂ) ^ (r i))
          = (∑ n ∈ Finset.Icc 1 K, a n * (n : ℂ) ^ (r i))
            + a (K + 1) * ((K : ℂ) + 1) ^ (r i) := by
        rw [Finset.sum_Icc_succ_top (by omega)]
        push_cast
        ring
      have := h i
      rw [hsplit, htop, zero_mul, add_zero] at this
      exact this
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rcases Nat.lt_or_ge n (K + 1) with hlt | hge
    · exact ih hrest n (Finset.mem_Icc.mpr ⟨hn.1, by omega⟩)
    · have : n = K + 1 := by omega
      rw [this]
      exact htop

end GaloisForLFunctions.RHTower

end
