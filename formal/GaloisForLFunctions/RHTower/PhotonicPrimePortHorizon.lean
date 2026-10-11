import GaloisForLFunctions.RHTower.LogZetaDirichletDivergence

/-!
# The prime-port horizon of route PTR

At grade `h > ½` the PTR producer `cos(hD)Ξ(x) = Re ξ(½ + h + ix)` is a prime-order readout. The
Euler product `ξ = ξ_∞ ∏_p (1 − p^{-s})^{-1}` converges absolutely on `Re s = ½ + h > 1`.

**Theorem** (`not_tendsto_ptrEulerPartialProduct`). For `½ < Re s < 1` the partial Euler products
`∏_{p ≤ N} (1 − p^{-s})^{-1}` converge to no nonzero limit, with or without RH.

So no grade `0 < h < ½` of the PTR producer is the limit of its own finite-prime ports at any
point where `ζ(s) ≠ 0`. The handoff from the prime source to the critical-strip grades cannot be
local in the primes: a nonlocal port, e.g. one with an approximate-functional-equation reflected
sum, is forced. This is the frontier-map requirement "nonlinear/nonlocal port", now a theorem.

**Proof.**
* If a product of nonzero factors tending to `1` converges to `L ≠ 0`, then the sums of the
  principal logarithms converge (`exists_tendsto_sum_log_of_tendsto_prod`). Their differences from
  a continuous logarithm of the partial products lie in `2πiℤ` and have increments tending to `0`.
* `−log(1 − z) = z + O(|z|²)`, and `Σ_p p^{-2σ}` converges for `σ > ½`. So the prime zeta series
  `Σ_p p^{-s}` would converge. It diverges on `Re s < 1`
  (`not_dirichletConvergesAt_primeIndicator`).
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- **Convergent products of factors tending to `1` have convergent logarithm sums.** -/
theorem exists_tendsto_sum_log_of_tendsto_prod {a : ℕ → ℂ} (ha0 : ∀ n, a n ≠ 0)
    (ha1 : Tendsto a atTop (𝓝 1)) {L : ℂ} (hL : L ≠ 0)
    (hP : Tendsto (fun N => ∏ n ∈ Finset.range N, a n) atTop (𝓝 L)) :
    ∃ M, Tendsto (fun N => ∑ n ∈ Finset.range N, Complex.log (a n)) atTop (𝓝 M) := by
  set P : ℕ → ℂ := fun N => ∏ n ∈ Finset.range N, a n with hPdef
  set S : ℕ → ℂ := fun N => ∑ n ∈ Finset.range N, Complex.log (a n) with hSdef
  have hP0 : ∀ N, P N ≠ 0 := fun N => Finset.prod_ne_zero_iff.mpr fun n _ => ha0 n
  have hexpS : ∀ N, Complex.exp (S N) = P N := by
    intro N
    simp only [hSdef, hPdef, Complex.exp_sum]
    exact Finset.prod_congr rfl fun n _ => Complex.exp_log (ha0 n)
  set ℓ : ℂ → ℂ := fun w => Complex.log (w / L) + Complex.log L with hℓ
  have hℓexp : ∀ N, Complex.exp (ℓ (P N)) = P N := by
    intro N
    simp only [hℓ, Complex.exp_add, Complex.exp_log (div_ne_zero (hP0 N) hL),
      Complex.exp_log hL]
    field_simp
  have hslit : (1 : ℂ) ∈ slitPlane := by simp [mem_slitPlane_iff]
  have hlogc : ContinuousAt Complex.log 1 := continuousAt_clog hslit
  have hℓc : ContinuousAt ℓ L := by
    have h1 : ContinuousAt (fun w : ℂ => w / L) L := continuousAt_id.div_const L
    have h2 : ContinuousAt (fun w : ℂ => Complex.log (w / L)) L := by
      refine ContinuousAt.comp (g := Complex.log) ?_ h1
      show ContinuousAt Complex.log (L / L)
      rw [div_self hL]; exact hlogc
    exact h2.add continuousAt_const
  set D : ℕ → ℂ := fun N => S N - ℓ (P N) with hD
  have hDint : ∀ N, ∃ k : ℤ, D N = k * (2 * Real.pi * I) := by
    intro N
    apply Complex.exp_eq_one_iff.mp
    show Complex.exp (S N - ℓ (P N)) = 1
    rw [Complex.exp_sub, hexpS, hℓexp, div_self (hP0 N)]
  have hstep : Tendsto (fun N => D (N + 1) - D N) atTop (𝓝 0) := by
    have hS : ∀ N, S (N + 1) - S N = Complex.log (a N) := by
      intro N; simp only [hSdef, Finset.sum_range_succ]; ring
    have h1 : Tendsto (fun N => Complex.log (a N)) atTop (𝓝 0) := by
      have := hlogc.tendsto.comp ha1
      rw [Complex.log_one] at this
      exact this
    have hPs : Tendsto (fun N => P (N + 1)) atTop (𝓝 L) := hP.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun N => ℓ (P (N + 1)) - ℓ (P N)) atTop (𝓝 0) := by
      have := (hℓc.tendsto.comp hPs).sub (hℓc.tendsto.comp hP)
      simpa using this
    have : (fun N => D (N + 1) - D N) =
        fun N => Complex.log (a N) - (ℓ (P (N + 1)) - ℓ (P N)) := by
      funext N; simp only [hD]; rw [← hS N]; ring
    rw [this]; simpa using h1.sub h2
  -- eventually the integer jumps vanish
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_iff_norm_sub_tendsto_zero.mp hstep).eventually (gt_mem_nhds hπ))
  have hconst : ∀ N, N₀ ≤ N → D (N + 1) = D N := by
    intro N hN
    have hlt := hN₀ N hN
    simp only [sub_zero] at hlt
    obtain ⟨k₁, hk₁⟩ := hDint (N + 1)
    obtain ⟨k₂, hk₂⟩ := hDint N
    rw [hk₁, hk₂, ← sub_mul, ← Int.cast_sub] at hlt
    set k := k₁ - k₂ with hkdef
    have hnorm : ‖((k : ℤ) : ℂ) * (2 * Real.pi * I)‖ = |(k : ℝ)| * (2 * Real.pi) := by
      rw [norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat, abs_of_pos Real.pi_pos]
    rw [hnorm] at hlt
    have hk : k = 0 := by
      by_contra hk0
      have : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
      nlinarith
    have hk12 : k₁ = k₂ := by omega
    rw [hk₁, hk₂, hk12]
  have hDN₀ : ∀ N, N₀ ≤ N → D N = D N₀ := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [hconst n hn, ih]
  refine ⟨ℓ L + D N₀, ?_⟩
  have hlim : Tendsto (fun N => ℓ (P N) + D N₀) atTop (𝓝 (ℓ L + D N₀)) :=
    (hℓc.tendsto.comp hP).add tendsto_const_nhds
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have := hDN₀ N hN
  simp only [hD] at this
  show ℓ (P N) + (S N₀ - ℓ (P N₀)) = S N
  rw [← this]; ring

/-- The `n`-th factor of the partial Euler product (index shifted by one). -/
def ptrEulerFactor (s : ℂ) (n : ℕ) : ℂ :=
  if (n + 1).Prime then (1 - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s))⁻¹ else 1

/-- The partial Euler product over the primes `p ≤ N`. -/
def ptrEulerPartialProduct (s : ℂ) (N : ℕ) : ℂ := ∏ n ∈ Finset.range N, ptrEulerFactor s n

/-- **The prime-port horizon.** For `½ < Re s < 1` the partial Euler products of `ζ` converge to
no nonzero limit. -/
theorem not_tendsto_ptrEulerPartialProduct {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re < 1) :
    ¬ ∃ L : ℂ, L ≠ 0 ∧ Tendsto (ptrEulerPartialProduct s) atTop (𝓝 L) := by
  rintro ⟨L, hL, hconv⟩
  set z : ℕ → ℂ := fun n => (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) with hz
  have hnorm : ∀ n : ℕ, ‖z n‖ = ((n : ℝ) + 1) ^ (-s.re) := by
    intro n
    simp only [hz]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
  have hσ : 0 < s.re := by linarith
  have hzle : ∀ n : ℕ, 1 ≤ n → ‖z n‖ ≤ (2 : ℝ) ^ (-s.re) := by
    intro n hn
    rw [hnorm]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith) (by linarith)
  have hq : (2 : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0 : 0 < (2 : ℝ) ^ (-s.re) := by positivity
  have hz0 : Tendsto z atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [hnorm]
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact (tendsto_rpow_neg_atTop hσ).comp h1
  -- the factors
  have hfac_ne : ∀ n, ptrEulerFactor s n ≠ 0 := by
    intro n
    unfold ptrEulerFactor
    split_ifs with hp
    · have hn : 1 ≤ n := by have := hp.two_le; omega
      refine inv_ne_zero fun h0 => ?_
      have : z n = 1 := by rw [hz]; linear_combination -h0
      have := hzle n hn
      rw [‹z n = 1›, norm_one] at this
      linarith
    · exact one_ne_zero
  have hfac1 : Tendsto (ptrEulerFactor s) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n => (1 - z n)⁻¹) atTop (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℂ))).sub hz0).inv₀ (by norm_num)
      simpa using this
    rw [tendsto_iff_norm_sub_tendsto_zero] at hinv ⊢
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hinv
    unfold ptrEulerFactor
    split_ifs
    · exact le_rfl
    · simp
  obtain ⟨M, hM⟩ := exists_tendsto_sum_log_of_tendsto_prod hfac_ne hfac1 hL hconv
  -- the second-order remainders are summable
  set R : ℕ → ℂ := fun n => if (n + 1).Prime then -Complex.log (1 - z n) - z n else 0 with hR
  have hRle : ∀ n, ‖R n‖ ≤ (1 - (2 : ℝ) ^ (-s.re))⁻¹ / 2 * ((n : ℝ) + 1) ^ (-(2 * s.re)) := by
    intro n
    simp only [hR]
    split_ifs with hp
    · have hn : 1 ≤ n := by have := hp.two_le; omega
      have hzn := hzle n hn
      have hlt : ‖-z n‖ < 1 := by rw [norm_neg]; linarith
      have h1 := Complex.norm_log_one_add_sub_self_le hlt
      rw [norm_neg] at h1
      have e : -Complex.log (1 - z n) - z n = -(Complex.log (1 + -z n) - -z n) := by
        rw [← sub_eq_add_neg]; ring
      rw [e, norm_neg]
      refine h1.trans ?_
      have hsq : ‖z n‖ ^ 2 = ((n : ℝ) + 1) ^ (-(2 * s.re)) := by
        rw [hnorm, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1; push_cast; ring
      rw [hsq]
      have hinv : (1 - ‖z n‖)⁻¹ ≤ (1 - (2 : ℝ) ^ (-s.re))⁻¹ :=
        inv_anti₀ (by linarith) (by linarith)
      have hpos : 0 ≤ ((n : ℝ) + 1) ^ (-(2 * s.re)) := by positivity
      calc ((n : ℝ) + 1) ^ (-(2 * s.re)) * (1 - ‖z n‖)⁻¹ / 2
          ≤ ((n : ℝ) + 1) ^ (-(2 * s.re)) * (1 - (2 : ℝ) ^ (-s.re))⁻¹ / 2 := by gcongr
        _ = _ := by ring
    · simp; positivity
  have hRsum : Summable R := by
    refine Summable.of_norm_bounded (g := fun n : ℕ =>
      (1 - (2 : ℝ) ^ (-s.re))⁻¹ / 2 * ((n : ℝ) + 1) ^ (-(2 * s.re))) ?_ hRle
    refine Summable.mul_left _ ?_
    have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (2 * s.re))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by linarith)
    have := (summable_nat_add_iff 1).mpr hbase
    refine this.congr fun n => ?_
    push_cast
    rw [Real.rpow_neg (by positivity)]
  -- the prime zeta series would converge
  apply GaloisForLFunctions.RHTower.not_dirichletConvergesAt_primeIndicator hs2
  refine ⟨M - ∑' n, R n, ?_⟩
  have hlogeq : ∀ n, Complex.log (ptrEulerFactor s n) =
      ((if (n + 1).Prime then (1 : ℝ) else 0 : ℝ) : ℂ) * z n + R n := by
    intro n
    simp only [ptrEulerFactor, hR]
    split_ifs with hp
    · have hn : 1 ≤ n := by have := hp.two_le; omega
      have hre : 0 < (1 - z n).re := by
        have := Complex.re_le_norm (z n)
        have h2 := hzle n hn
        simp only [Complex.sub_re, Complex.one_re]
        have := Complex.abs_re_le_norm (z n)
        linarith [neg_abs_le (z n).re]
      have harg : (1 - z n).arg ≠ Real.pi := by
        intro h
        have := Complex.arg_eq_pi_iff.mp h
        linarith [this.1]
      rw [Complex.log_inv _ harg]
      push_cast; ring
    · simp
  have hsplit : (fun N => ∑ n ∈ Finset.range N,
      ((if (n + 1).Prime then (1 : ℝ) else 0 : ℝ) : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) =
      fun N => (∑ n ∈ Finset.range N, Complex.log (ptrEulerFactor s n)) -
        ∑ n ∈ Finset.range N, R n := by
    funext N
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hlogeq n]; ring
  rw [hsplit]
  exact hM.sub hRsum.hasSum.tendsto_sum_nat

end

end RHTower
