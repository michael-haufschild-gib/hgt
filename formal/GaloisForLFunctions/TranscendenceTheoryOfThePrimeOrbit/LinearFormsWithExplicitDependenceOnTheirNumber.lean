import GaloisForLFunctions.RHTower.Matveev.EffectiveBaker

/-!
# Linear forms with explicit dependence on their number

Fel'dman's method gives, for distinct primes `p₁, …, p_k` with `Σ log p_i ≤ W` and every nonzero
`ν ∈ ℤ^k`,

`|Σ ν_i log p_i| ≥ exp(−C(k, W)(log |ν|₁ + 2))`.

The corpus proves this with an existential `C` (`RHTower.Matveev.effectiveBakerBound_holds`): the
number `R` of extrapolation steps is taken from `poly(R) ≤ 2^R` by a limit. Here `R` is explicit,

`R = L + 2D(⌊log₂(L + D + 1)⌋ + 1)`,  `L = 2 + k(k+1)(⌊log₂ 1000W⌋ + 1)`,  `D = k(k+2)`,

and every Fel'dman parameter is a power of `U = 10⁴(W + 1)(k + 1)²`. The result
(`abs_primeLogForm_ge_explicit`) is

`C(k, W) ≤ U^{30(k+1)²} = exp(30(k+1)² log(10⁴(W+1)(k+1)²))`:

the exponent grows like `k² log(kW)`.

**Necessity.** Dirichlet's pigeonhole principle on `{0, …, H}^k` gives a nonzero `ν` with
`|ν_i| ≤ H` and `|Λ_ν| ≤ W/H^{k−1}` (`exists_small_primeLogForm`); hence no bound
`c(2 + |ν|₁)^{−C}` holds with `C < k − 1` (`le_exponent_of_bakerBound`). The exponent of any lower
bound for linear forms in `k` logarithms grows at least linearly in `k`.

**At `k ≍ π(y)`.** With `W ≤ k log y` the explicit exponent is `exp(O(y²/log y))`, and the Liouville
bound `|Λ_ν| ≥ y^{−|ν|₁}` is better at every height `|ν|₁ ≤ exp(c y²/log y)`; at precision `δ` only
heights `< 1/2δ` act on returns (`TheReturnFormDuality`).
-/

namespace GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section

open Finset Real
open RHTower.Matveev

variable {m : ℕ}

/-! ## Fel'dman's bound for given parameters -/

/-- **Fel'dman's pivot bound at given parameters.** The proof of
`RHTower.Matveev.exists_feldman_pivot_bound`, with the parameters `P` as input. -/
theorem feldman_pivot_bound_of_params {Wb : ℕ} (P : FeldmanParams m (Wb + 1))
    (p : Fin (m + 1) → ℕ) (hpinj : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (hW : totalLogSum p ≤ Wb) (b : Fin (m + 1) → ℤ) (hB : 0 < b (Fin.last m))
    (hb : ∀ j, |b j| ≤ b (Fin.last m)) :
    Real.exp (-((feldmanLambdaExponent P + 1) * (Real.log (b (Fin.last m)) + 2))) ≤
      |primeLogForm p b| := by
  set C₀ := feldmanLambdaExponent P + 1 with hC₀
  have hp1 : ∀ j, 1 ≤ p j := fun j => (hprime j).one_lt.le
  set B : ℝ := (b (Fin.last m) : ℝ) with hBdef
  have hB1 : (1 : ℝ) ≤ B := by rw [hBdef]; exact_mod_cast hB
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  set n := ⌈Real.log B⌉₊ + 1 with hn
  have hn1 : 1 ≤ n := by omega
  have hBn : Real.log B ≤ n := by
    have := Nat.le_ceil (Real.log B)
    rw [hn]; push_cast; linarith
  have hnB : (n : ℝ) ≤ Real.log B + 2 := by
    have := Nat.ceil_lt_add_one hlogB
    rw [hn]; push_cast; linarith
  have hC₀0 : 0 < C₀ := by rw [hC₀]; linarith [feldmanLambdaExponent_nonneg P]
  by_contra hcontra
  push Not at hcontra
  set lam := primeLogForm p b with hlam
  have hlamn : |lam| < Real.exp (-((feldmanLambdaExponent P + 1) * n)) := by
    refine hcontra.trans_le (Real.exp_le_exp.mpr ?_)
    rw [← hC₀]
    nlinarith
  -- the parameters
  set N := P.a * n with hN
  set X₀ := P.c * n with hX₀
  have hq1 := P.one_le_q
  have hX₀1 : 1 ≤ X₀ := by rw [hX₀]; exact Nat.one_le_iff_ne_zero.mpr (by
    have := P.one_le_c; positivity)
  have hS : 0 < P.S := by rw [P.S_eq]; omega
  have ha1 : 1 ≤ P.a := by
    by_contra h
    have h0 : P.a = 0 := by omega
    have := P.siegel
    rw [h0, zero_mul] at this
    have : 0 < 2 * P.c * P.S ^ (m + 1) := by have := P.one_le_c; positivity
    omega
  have hcount : 2 * (X₀ * P.S ^ (m + 1)) ≤ (N + 1) * P.q ^ (m + 1) := by
    have h := Nat.mul_le_mul_right n P.siegel
    calc 2 * (X₀ * P.S ^ (m + 1)) = 2 * P.c * P.S ^ (m + 1) * n := by rw [hX₀]; ring
      _ ≤ P.a * P.q ^ (m + 1) * n := h
      _ = N * P.q ^ (m + 1) := by rw [hN]; ring
      _ ≤ (N + 1) * P.q ^ (m + 1) := Nat.mul_le_mul_right _ (Nat.le_succ N)
  set Wt := totalLogSum p with hWt
  have hWt0 : 0 ≤ Wt := totalLogSum_nonneg p hp1
  have hWtb : Wt ≤ ((Wb + 1 : ℕ) : ℝ) := by push_cast; linarith
  set W := baseLogSum p with hWdef
  have hW0 : 0 ≤ W := baseLogSum_nonneg p hp1
  have hWb : W ≤ ((Wb + 1 : ℕ) : ℝ) := (baseLogSum_le_totalLogSum p hp1).trans hWtb
  have hAmax : 0 ≤ feldmanCoeffBound m N P.q P.S X₀ B Wt := by
    unfold feldmanCoeffBound
    have : (0 : ℝ) < feldmanDivisor (N + 1) P.S := by exact_mod_cast feldmanDivisor_pos _ _
    positivity
  obtain ⟨C, hC0, hCvan, hCbound⟩ := exists_feldmanSiegel p b (by omega) hS hcount hAmax
    (fun x hx σ hσ τ hτ kl => abs_feldmanCoeff_le_bound hp1 hB hb hq1 hx hσ hτ kl)
  -- the initial vanishing
  have h0 : ∀ x < X₀, ∀ σ (τ : Fin m → ℕ), σ + ∑ j, τ j < P.S →
      feldmanTrueAux p b N P.q C σ τ (x : ℂ) = 0 := by
    intro x hx σ τ hστ
    have hτ : ∀ j, τ j < P.S := fun j => by
      have := single_le_sum (f := τ) (fun i _ => Nat.zero_le _) (mem_univ j)
      omega
    have hrel := pow_mul_feldmanTrueAux_natCast p b (fun j => (hprime j).pos) hB.ne' C
      (show σ < P.S by omega) τ x
    rw [hCvan x hx σ (by omega) τ hτ, Int.cast_zero, mul_zero] at hrel
    exact (mul_eq_zero.mp hrel).resolve_left (pow_ne_zero _ (by exact_mod_cast hB.ne'))
  -- the extrapolation
  have hΛ : 8 * ((2 ^ P.R * X₀ : ℕ) : ℝ) * P.q * |lam| ≤ 1 := by
    have hy : 8 * ((2 ^ P.R * X₀ : ℕ) : ℝ) * P.q ≤ (feldmanLambdaExponent P + 1) * n := by
      have h16 := sixteen_mul_le_feldmanLambdaExponent P
      have hcast : ((2 ^ P.R * X₀ : ℕ) : ℝ) = (2 : ℝ) ^ P.R * P.c * n := by
        rw [hX₀]; push_cast; ring
      rw [hcast]
      have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hpos : (0 : ℝ) ≤ 16 * ((2 : ℝ) ^ P.R * P.c) * P.q := by positivity
      nlinarith
    have hy0 : 0 ≤ 8 * ((2 ^ P.R * X₀ : ℕ) : ℝ) * P.q := by positivity
    calc 8 * ((2 ^ P.R * X₀ : ℕ) : ℝ) * P.q * |lam|
        ≤ Real.exp ((feldmanLambdaExponent P + 1) * n) *
            Real.exp (-((feldmanLambdaExponent P + 1) * n)) :=
          mul_le_mul (hy.trans (le_exp_self' _)) hlamn.le (abs_nonneg _) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hext := feldman_extrapolation p b hp1 hB hb hq1 C hCbound feldmanCmax_nonneg
    (X₀ := X₀) (T₀ := P.S) (M := P.M) (R := P.R) hX₀1 le_rfl (by rw [P.S_eq]; omega) hΛ h0
    (fun r hr => feldman_stage_threshold P hn1 hr hB1 hBn hW0 hWb hWt0 hWtb hlamn)
  -- the terminal vanishing
  have hterm : (N + 1) * P.q ^ (m + 1) ≤ 2 ^ P.R * X₀ := by
    have h := Nat.mul_le_mul_right n P.terminal
    calc (N + 1) * P.q ^ (m + 1) ≤ 2 * N * P.q ^ (m + 1) := by
          refine Nat.mul_le_mul_right _ ?_
          rw [hN]; nlinarith
      _ = 2 * P.a * P.q ^ (m + 1) * n := by rw [hN]; ring
      _ ≤ 2 ^ P.R * P.c * n := h
      _ = 2 ^ P.R * X₀ := by rw [hX₀]; ring
  have hCzero := eq_zero_of_feldmanTrueAux_eq_zero p b hpinj hprime C fun x hx =>
    hext x (by omega) 0 0 (by rw [P.S_eq]; simp)
  exact hC0 hCzero

/-! ## Explicit parameters -/

/-- The Fel'dman parameters built from a given number `R` of extrapolation steps. -/
theorem exists_feldmanParams_of_R (m Wb R : ℕ) (hWb : 1 ≤ Wb) (hR1 : 1 ≤ R)
    (hR : 4 * (1000 * Wb) ^ ((m + 1) * (m + 2)) * (R + 1) ^ ((m + 1) * (m + 2) + (m + 1)) ≤ 2 ^ R) :
    ∃ P : FeldmanParams m Wb, P.R = R ∧
      P.q = (1000 * Wb * (R + 1)) ^ (m + 1) * (R + 1) ∧
      P.M = 1000 * Wb * ((1000 * Wb * (R + 1)) ^ (m + 1) * (R + 1)) ∧
      P.S = R * (1000 * Wb * ((1000 * Wb * (R + 1)) ^ (m + 1) * (R + 1))) + 1 ∧
      P.c = 16 * (m + 1) * (R + 1) * ((1000 * Wb * (R + 1)) ^ (m + 1) * (R + 1)) ∧
      P.a = 2 * (16 * (m + 1) * (R + 1) * ((1000 * Wb * (R + 1)) ^ (m + 1) * (R + 1))) *
        (1000 * Wb * (R + 1)) ^ (m + 1) := by
  obtain ⟨E, hE⟩ : ∃ E, E = 1000 * Wb * (R + 1) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = E ^ (m + 1) * (R + 1) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = 1000 * Wb * q := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = R * M + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = 16 * (m + 1) * (R + 1) * q := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = 2 * c * E ^ (m + 1) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hc1 : 1 ≤ c := by rw [hc]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpoly : 4 * E ^ (m + 1) * q ^ (m + 1) ≤ 2 ^ R := by
    rw [hq, feldman_pow_identity E R Wb m hE]; exact hR
  have hWq : 1 ≤ Wb * q := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hSEq : S ≤ E * q := by
    have h1 : E * q = R * (1000 * Wb * q) + 1000 * (Wb * q) := by rw [hE]; ring
    rw [hS, hM, h1]
    omega
  have hEq : E * q ≤ 4 * E ^ (m + 1) * q ^ (m + 1) := by
    have h1 : E ≤ E ^ (m + 1) := Nat.le_self_pow (Nat.succ_ne_zero m) E
    have h2 : q ≤ q ^ (m + 1) := Nat.le_self_pow (Nat.succ_ne_zero m) q
    calc E * q ≤ E ^ (m + 1) * q ^ (m + 1) := Nat.mul_le_mul h1 h2
      _ ≤ 4 * E ^ (m + 1) * q ^ (m + 1) := by
          rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ (by norm_num)
  have haq : a = 32 * ((m + 1) * q * q) := by
    rw [ha, hc, hq]; ring
  refine ⟨⟨R, M, q, S, c, a, hR1, hq1, hc1, hS, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have h : 1000 * Wb * q = 1000 * (Wb * q) := by ring
    have h' : 4 * (9 + 17 * q * Wb) = 36 + 68 * (Wb * q) := by ring
    rw [hM, h, h']
    omega
  · calc 2 * c * S ^ (m + 1) ≤ 2 * c * (E * q) ^ (m + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hSEq _)
      _ = a * q ^ (m + 1) := by rw [ha, mul_pow]; ring
  · calc 2 * a * q ^ (m + 1) = c * (4 * E ^ (m + 1) * q ^ (m + 1)) := by rw [ha]; ring
      _ ≤ c * 2 ^ R := Nat.mul_le_mul_left _ hpoly
      _ = 2 ^ R * c := by ring
  · have hlt : S < 2 ^ (R + 1) := by
      calc S ≤ 2 ^ R := hSEq.trans (hEq.trans hpoly)
        _ < 2 ^ (R + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self R)
    have := Nat.log_lt_of_lt_pow (show S ≠ 0 by rw [hS]; omega) hlt
    omega
  · -- the gain inequality
    obtain ⟨u, hu⟩ : ∃ u, u = (m + 1) * Wb * q * q := ⟨_, rfl⟩
    have hu1 : 1 ≤ u := by rw [hu]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hRWq : 1 ≤ R * Wb * q := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hSle : S ≤ 1001 * (R * Wb * q) := by
      have h : R * M = 1000 * (R * Wb * q) := by rw [hM]; ring
      rw [hS, h]; omega
    have h1 : (m + 1) * S * (1 + 2 * q) ≤ 3003 * R * u := by
      calc (m + 1) * S * (1 + 2 * q) ≤ (m + 1) * (1001 * (R * Wb * q)) * (3 * q) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hSle) (by omega)
        _ = 3003 * R * u := by rw [hu]; ring
    have hqq : (m + 1) * q * q ≤ u := by
      rw [hu]
      calc (m + 1) * q * q = (m + 1) * 1 * q * q := by ring
        _ ≤ (m + 1) * Wb * q * q := by gcongr
    have h2 : 4 * a ≤ 128 * u := by
      rw [haq]
      calc 4 * (32 * ((m + 1) * q * q)) = 128 * ((m + 1) * q * q) := by ring
        _ ≤ 128 * u := Nat.mul_le_mul_left _ hqq
    have h3 : 2 * (m + 1) * q ≤ 2 * u := by
      have : (m + 1) * q ≤ (m + 1) * q * q := Nat.le_mul_of_pos_right _ (by omega)
      calc 2 * (m + 1) * q = 2 * ((m + 1) * q) := by ring
        _ ≤ 2 * u := Nat.mul_le_mul_left _ (this.trans hqq)
    have h4 : 2 * (a + 1) * (19 + 12 * R) ≤ 66 * u * (19 + 12 * R) := by
      have ha1 : a + 1 ≤ 33 * u := by
        rw [haq]
        have := Nat.mul_le_mul_left 32 hqq
        omega
      calc 2 * (a + 1) * (19 + 12 * R) ≤ 2 * (33 * u) * (19 + 12 * R) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ha1)
        _ = 66 * u * (19 + 12 * R) := by ring
    calc 4 * ((m + 1) * S * (1 + 2 * q) + 4 * a + 2 * (m + 1) * q + 2 * (a + 1) * (19 + 12 * R)
          + 1)
        ≤ 4 * (3003 * R * u + 128 * u + 2 * u + 66 * u * (19 + 12 * R) + u) := by gcongr
      _ = u * (15180 * R + 5540) := by ring
      _ ≤ u * (48000 * (R + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * M * c := by rw [hM, hc, hu]; ring
  · show q = _; rw [hq, hE]
  · show M = _; rw [hM, hq, hE]
  · show S = _; rw [hS, hM, hq, hE]
  · show c = _; rw [hc, hq, hE]
  · show a = _; rw [ha, hc, hq, hE]


/-! ## An explicit number of extrapolation steps -/

/-- `L = 2 + (m+1)(m+2)(⌊log₂ 1000W⌋ + 1)`, so that `4(1000W)^{(m+1)(m+2)} ≤ 2^L`. -/
def explicitL (m Wb : ℕ) : ℕ := 2 + (m + 1) * (m + 2) * (Nat.log 2 (1000 * Wb) + 1)

/-- The degree `D = (m+1)(m+2) + (m+1)` of the polynomial factor `(R+1)^D`. -/
def explicitD (m : ℕ) : ℕ := (m + 1) * (m + 2) + (m + 1)

/-- `B = ⌊log₂(L + D + 1)⌋ + 1`, so that `L + D + 1 < 2^B`. -/
def explicitB (m Wb : ℕ) : ℕ := Nat.log 2 (explicitL m Wb + explicitD m + 1) + 1

/-- The explicit number of extrapolation steps `R = L + 2DB`. -/
def explicitR (m Wb : ℕ) : ℕ := explicitL m Wb + explicitD m * (2 * explicitB m Wb)

theorem two_mul_le_two_pow {b : ℕ} (hb : 1 ≤ b) : 2 * b ≤ 2 ^ b := by
  induction b with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · have := ih h
      have h2 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
      rw [pow_succ]; omega

theorem log_two_lt_self {x : ℕ} (hx : x ≠ 0) : Nat.log 2 x < x :=
  (Nat.lt_two_pow_self).trans_le (Nat.pow_log_le_self 2 hx)

/-- The explicit `R` satisfies `4(1000W)^{(m+1)(m+2)}(R+1)^D ≤ 2^R`. -/
theorem explicitR_spec (m Wb : ℕ) :
    4 * (1000 * Wb) ^ ((m + 1) * (m + 2)) * (explicitR m Wb + 1) ^ ((m + 1) * (m + 2) + (m + 1)) ≤
      2 ^ explicitR m Wb := by
  set L := explicitL m Wb
  set D := explicitD m
  set B := explicitB m Wb
  have hK : 4 * (1000 * Wb) ^ ((m + 1) * (m + 2)) ≤ 2 ^ L := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (1000 * Wb)
    have h' : (1000 * Wb) ^ ((m + 1) * (m + 2)) ≤
        (2 ^ (Nat.log 2 (1000 * Wb) + 1)) ^ ((m + 1) * (m + 2)) := Nat.pow_le_pow_left h.le _
    calc 4 * (1000 * Wb) ^ ((m + 1) * (m + 2))
        ≤ 2 ^ 2 * (2 ^ (Nat.log 2 (1000 * Wb) + 1)) ^ ((m + 1) * (m + 2)) := by
          rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact Nat.mul_le_mul_left _ h'
      _ = 2 ^ L := by
          simp only [L, explicitL, ← pow_mul, ← pow_add]; ring_nf
  have hB1 : 1 ≤ B := Nat.le_add_left 1 _
  have haB : L + D + 1 < 2 ^ B := Nat.lt_pow_succ_log_self (by norm_num) _
  have hR1 : explicitR m Wb + 1 ≤ 2 ^ (2 * B) := by
    have hs : explicitR m Wb + 1 ≤ (L + D + 1) * (2 * B) := by
      simp only [explicitR]
      nlinarith
    calc explicitR m Wb + 1 ≤ (L + D + 1) * (2 * B) := hs
      _ ≤ 2 ^ B * 2 ^ B := Nat.mul_le_mul haB.le (two_mul_le_two_pow hB1)
      _ = 2 ^ (2 * B) := by rw [← pow_add]; ring_nf
  calc 4 * (1000 * Wb) ^ ((m + 1) * (m + 2)) * (explicitR m Wb + 1) ^ D
      ≤ 2 ^ L * (2 ^ (2 * B)) ^ D := Nat.mul_le_mul hK (Nat.pow_le_pow_left hR1 _)
    _ = 2 ^ explicitR m Wb := by
        rw [← pow_mul, ← pow_add]; congr 1; simp only [explicitR, L, D, B]; ring

theorem one_le_explicitR (m Wb : ℕ) : 1 ≤ explicitR m Wb := by
  simp only [explicitR, explicitL]; omega

/-! ## Every parameter is a power of `U` -/

/-- The base `U = 10⁴ W (m+2)²` of the explicit bounds. -/
def baseU (m Wb : ℕ) : ℕ := 10 ^ 4 * Wb * (m + 2) ^ 2

/-- The explicit exponent `C(m+1, W) = U^{30(m+2)²}` for `m + 1` logarithms with `Σ log p ≤ W`,
`U = 10⁴(W+1)(m+2)²`. -/
def bakerExponent (m Wb : ℕ) : ℝ := (baseU m (Wb + 1) : ℝ) ^ (30 * (m + 2) ^ 2)

section Bounds

variable {m Wb : ℕ}

theorem le_baseU_of_le {x : ℕ} (h : x ≤ 2500 * Wb) : x ≤ baseU m Wb := by
  simp only [baseU]
  have : 1 ≤ (m + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem sq_le_baseU (hWb : 1 ≤ Wb) : (m + 2) ^ 2 ≤ baseU m Wb := by
  simp only [baseU]; nlinarith

theorem ten_four_le_baseU (hWb : 1 ≤ Wb) : 10 ^ 4 ≤ baseU m Wb := by
  simp only [baseU]
  have : 1 ≤ (m + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem explicitD_le : explicitD m ≤ (m + 2) ^ 2 := by
  simp only [explicitD]; nlinarith

theorem explicitL_le (hWb : 1 ≤ Wb) : explicitL m Wb + explicitD m + 1 ≤ baseU m Wb := by
  have hu : Nat.log 2 (1000 * Wb) + 1 ≤ 1000 * Wb := log_two_lt_self (by omega)
  have hD := explicitD_le (m := m)
  have hmm : (m + 1) * (m + 2) ≤ (m + 2) ^ 2 := by nlinarith
  simp only [explicitL, baseU]
  have h1 : (m + 1) * (m + 2) * (Nat.log 2 (1000 * Wb) + 1) ≤ (m + 2) ^ 2 * (1000 * Wb) :=
    Nat.mul_le_mul hmm hu
  have : 4 ≤ (m + 2) ^ 2 := by nlinarith
  nlinarith

theorem explicitR_add_one_le (hWb : 1 ≤ Wb) : explicitR m Wb + 1 ≤ baseU m Wb ^ 3 := by
  have hU := ten_four_le_baseU (m := m) hWb
  have hL := explicitL_le (m := m) hWb
  have hB : explicitB m Wb ≤ baseU m Wb := by
    have : explicitB m Wb ≤ explicitL m Wb + explicitD m + 1 :=
      log_two_lt_self (by omega)
    omega
  have hD : explicitD m ≤ baseU m Wb := explicitD_le.trans (sq_le_baseU hWb)
  have h1 : explicitD m * (2 * explicitB m Wb) ≤ baseU m Wb * (2 * baseU m Wb) :=
    Nat.mul_le_mul hD (by omega)
  have hL' : explicitL m Wb ≤ baseU m Wb := by omega
  set U := baseU m Wb
  have h2 : U * (2 * U) + U + 1 ≤ U ^ 3 := by
    have hUU : 10 ^ 4 * (U * U) ≤ U * (U * U) := Nat.mul_le_mul_right _ hU
    have hU2 : U + 1 ≤ U * U := by nlinarith
    have e3 : U ^ 3 = U * (U * U) := by ring
    have e2 : U * (2 * U) = 2 * (U * U) := by ring
    rw [e3, e2]; linarith
  simp only [explicitR]
  omega

theorem two_pow_explicitR_le (hWb : 1 ≤ Wb) :
    2 ^ explicitR m Wb ≤ baseU m Wb ^ (5 * (m + 2) ^ 2 + 1) := by
  set U := baseU m Wb
  have hU := ten_four_le_baseU (m := m) hWb
  have hU1 : 1 ≤ U := by omega
  -- `2^L ≤ 4 U^{(m+1)(m+2)}`
  have hu : 2 ^ (Nat.log 2 (1000 * Wb) + 1) ≤ U := by
    have h := Nat.pow_log_le_self 2 (show 1000 * Wb ≠ 0 by omega)
    rw [pow_succ]
    exact le_baseU_of_le (by omega)
  have hmm : (m + 1) * (m + 2) ≤ (m + 2) ^ 2 := by nlinarith
  have hL : 2 ^ explicitL m Wb ≤ U * U ^ ((m + 2) ^ 2) := by
    have e : 2 ^ explicitL m Wb = 2 ^ 2 * (2 ^ (Nat.log 2 (1000 * Wb) + 1)) ^ ((m + 1) * (m + 2)) := by
      simp only [explicitL]; rw [pow_add, ← pow_mul]; congr 2; ring
    rw [e]
    calc 2 ^ 2 * (2 ^ (Nat.log 2 (1000 * Wb) + 1)) ^ ((m + 1) * (m + 2))
        ≤ U * U ^ ((m + 1) * (m + 2)) :=
          Nat.mul_le_mul (by norm_num; omega) (Nat.pow_le_pow_left hu _)
      _ ≤ U * U ^ ((m + 2) ^ 2) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hU1 hmm)
  -- `(2^B)^{2D} ≤ U^{4(m+2)²}`
  have hB : 2 ^ explicitB m Wb ≤ U * U := by
    have h := Nat.pow_log_le_self 2 (show explicitL m Wb + explicitD m + 1 ≠ 0 by omega)
    have hL' := explicitL_le (m := m) hWb
    simp only [explicitB, pow_succ]
    nlinarith
  have hBD : (2 ^ explicitB m Wb) ^ (2 * explicitD m) ≤ U ^ (4 * (m + 2) ^ 2) := by
    calc (2 ^ explicitB m Wb) ^ (2 * explicitD m) ≤ (U * U) ^ (2 * explicitD m) :=
          Nat.pow_le_pow_left hB _
      _ = U ^ (4 * explicitD m) := by rw [← pow_two, ← pow_mul]; ring_nf
      _ ≤ U ^ (4 * (m + 2) ^ 2) := Nat.pow_le_pow_right hU1 (by have := explicitD_le (m := m); omega)
  calc 2 ^ explicitR m Wb = 2 ^ explicitL m Wb * (2 ^ explicitB m Wb) ^ (2 * explicitD m) := by
        simp only [explicitR, pow_add, ← pow_mul]; ring_nf
    _ ≤ (U * U ^ ((m + 2) ^ 2)) * U ^ (4 * (m + 2) ^ 2) := Nat.mul_le_mul hL hBD
    _ = U ^ (5 * (m + 2) ^ 2 + 1) := by ring

end Bounds


/-! ## The explicit exponent -/

theorem exponent_le (m : ℕ) : 1 + (5 * (m + 2) ^ 2 + 1) + 3 * (8 * m + 16) ≤ 30 * (m + 2) ^ 2 := by
  nlinarith

/-- The polynomial that dominates `λ(P)` once every parameter is replaced by `v ≥ 1` and `2^R` by
`Z ≥ 1`; its coefficients add up to `200`. -/
theorem lambda_polynomial_le {v Z : ℝ} (hv1 : 1 ≤ v) (hZ1 : 1 ≤ Z) :
    v + 2 * v + 2 * (v + 1) * v + v + v + (v + 1) * (19 + 12 * v) +
      2 * v * v * v + v * v + v * v * v + v + 8 * (Z * v) +
      (v + 1) * (19 + 12 * v) + 2 * v * v + 8 * (Z * v) * v * v +
      16 * (Z * v) * v + 5 + (Z * v) + v * (v + v) + 9 * (Z * v) +
      v + 10 * v ^ 2 * (Z * v) ≤ 200 * Z * v ^ 3 := by
  have h1 : v ≤ v ^ 3 := le_self_pow₀ hv1 (by norm_num)
  have h2 : v ^ 2 ≤ v ^ 3 := pow_le_pow_right₀ hv1 (by norm_num)
  have h0 : (1 : ℝ) ≤ v ^ 3 := one_le_pow₀ hv1
  have hZ : v ^ 3 ≤ Z * v ^ 3 := le_mul_of_one_le_left (by positivity) hZ1
  have hZv : Z * v ≤ Z * v ^ 3 := mul_le_mul_of_nonneg_left h1 (by linarith)
  have hZv2 : Z * v ^ 2 ≤ Z * v ^ 3 := mul_le_mul_of_nonneg_left h2 (by linarith)
  have e : v + 2 * v + 2 * (v + 1) * v + v + v + (v + 1) * (19 + 12 * v) +
      2 * v * v * v + v * v + v * v * v + v + 8 * (Z * v) +
      (v + 1) * (19 + 12 * v) + 2 * v * v + 8 * (Z * v) * v * v +
      16 * (Z * v) * v + 5 + (Z * v) + v * (v + v) + 9 * (Z * v) +
      v + 10 * v ^ 2 * (Z * v) =
      3 * v ^ 3 + 18 * (Z * v ^ 3) + 16 * (Z * v ^ 2) + 18 * (Z * v) + 31 * v ^ 2 + 71 * v + 43 := by
    ring
  rw [e]
  linarith

/-- **The Fel'dman exponent is a power of `U`.** For the explicit parameters,
`C₀ = λ(P) + 1 ≤ U^{30(m+2)²}`. -/
theorem feldmanLambdaExponent_add_one_le {Wb : ℕ} (hWb : 1 ≤ Wb) (P : FeldmanParams m Wb)
    (hR : P.R = explicitR m Wb)
    (hq : P.q = (1000 * Wb * (explicitR m Wb + 1)) ^ (m + 1) * (explicitR m Wb + 1))
    (hM : P.M = 1000 * Wb * ((1000 * Wb * (explicitR m Wb + 1)) ^ (m + 1) * (explicitR m Wb + 1)))
    (hS : P.S = explicitR m Wb *
      (1000 * Wb * ((1000 * Wb * (explicitR m Wb + 1)) ^ (m + 1) * (explicitR m Wb + 1))) + 1)
    (hc : P.c = 16 * (m + 1) * (explicitR m Wb + 1) *
      ((1000 * Wb * (explicitR m Wb + 1)) ^ (m + 1) * (explicitR m Wb + 1)))
    (ha : P.a = 2 * (16 * (m + 1) * (explicitR m Wb + 1) *
      ((1000 * Wb * (explicitR m Wb + 1)) ^ (m + 1) * (explicitR m Wb + 1))) *
        (1000 * Wb * (explicitR m Wb + 1)) ^ (m + 1)) :
    feldmanLambdaExponent P + 1 ≤ (baseU m Wb : ℝ) ^ (30 * (m + 2) ^ 2) := by
  have hU := ten_four_le_baseU (m := m) hWb
  have hR1 := explicitR_add_one_le (m := m) hWb
  have hW : 1000 * Wb ≤ baseU m Wb := le_baseU_of_le (by omega)
  have hm : 16 * (m + 1) ≤ baseU m Wb := by
    have := sq_le_baseU (m := m) hWb
    have h10 : 16 * (m + 1) ≤ 10 ^ 4 * Wb * (m + 2) ^ 2 := by nlinarith
    exact h10
  have h2R : 2 ^ P.R ≤ baseU m Wb ^ (5 * (m + 2) ^ 2 + 1) := hR ▸ two_pow_explicitR_le hWb
  have hexp := exponent_le m
  generalize baseU m Wb = U at hU hR1 hW hm h2R ⊢
  generalize explicitR m Wb = R at hR hq hM hS hc ha hR1
  have hU1 : 1 ≤ U := by omega
  -- the parameters as powers of `U`
  have hE : 1000 * Wb * (R + 1) ≤ U ^ 4 := by
    calc 1000 * Wb * (R + 1) ≤ U * U ^ 3 := Nat.mul_le_mul hW hR1
      _ = U ^ 4 := by ring
  have hEm : (1000 * Wb * (R + 1)) ^ (m + 1) ≤ U ^ (4 * m + 4) := by
    calc (1000 * Wb * (R + 1)) ^ (m + 1) ≤ (U ^ 4) ^ (m + 1) := Nat.pow_le_pow_left hE _
      _ = U ^ (4 * m + 4) := by rw [← pow_mul]; ring_nf
  have hq' : P.q ≤ U ^ (4 * m + 7) := by
    rw [hq]
    calc (1000 * Wb * (R + 1)) ^ (m + 1) * (R + 1) ≤ U ^ (4 * m + 4) * U ^ 3 :=
          Nat.mul_le_mul hEm hR1
      _ = U ^ (4 * m + 7) := by ring
  have hM' : P.M ≤ U ^ (4 * m + 8) := by
    rw [hM, ← hq]
    calc 1000 * Wb * P.q ≤ U * U ^ (4 * m + 7) := Nat.mul_le_mul hW hq'
      _ = U ^ (4 * m + 8) := by ring
  have hS' : P.S ≤ U ^ (4 * m + 11) := by
    have hSR : P.S ≤ (R + 1) * P.M := by
      rw [hS, ← hM]; have : 1 ≤ P.M := by rw [hM]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    calc P.S ≤ (R + 1) * P.M := hSR
      _ ≤ U ^ 3 * U ^ (4 * m + 8) := Nat.mul_le_mul hR1 hM'
      _ = U ^ (4 * m + 11) := by ring
  have hc' : P.c ≤ U ^ (4 * m + 11) := by
    rw [hc, ← hq]
    calc 16 * (m + 1) * (R + 1) * P.q ≤ U * U ^ 3 * U ^ (4 * m + 7) :=
          Nat.mul_le_mul (Nat.mul_le_mul hm hR1) hq'
      _ = U ^ (4 * m + 11) := by ring
  have hc2 : P.c = 16 * (m + 1) * (R + 1) * P.q := by rw [hc, hq]
  have ha' : P.a ≤ U ^ (8 * m + 16) := by
    rw [ha, ← hq, ← hc2]
    calc 2 * P.c * (1000 * Wb * (R + 1)) ^ (m + 1) ≤ U * U ^ (4 * m + 11) * U ^ (4 * m + 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) hc') hEm
      _ = U ^ (8 * m + 16) := by ring
  -- one bound `V = U^{8m+16}` for every parameter
  set V := U ^ (8 * m + 16) with hV
  have hpow : ∀ k, k ≤ 8 * m + 16 → U ^ k ≤ V := fun k hk => Nat.pow_le_pow_right hU1 hk
  have hRV : P.R ≤ V := by
    rw [hR]; exact (Nat.le_succ R).trans (hR1.trans (hpow 3 (by omega)))
  have hqV := hq'.trans (hpow _ (by omega))
  have hMV := hM'.trans (hpow _ (by omega))
  have hSV := hS'.trans (hpow _ (by omega))
  have hcV := hc'.trans (hpow _ (by omega))
  have hWV : Wb ≤ V := (show Wb ≤ U by omega).trans (by simpa using hpow 1 (by omega))
  have hmV : m ≤ V := (show m ≤ U by omega).trans (by simpa using hpow 1 (by omega))
  -- the real bound
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = (V : ℝ) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = (2 : ℝ) ^ P.R := ⟨_, rfl⟩
  have hv1 : (1 : ℝ) ≤ v := by
    have : 1 ≤ V := Nat.one_le_pow _ _ (by omega)
    rw [hv]; exact_mod_cast this
  have hZ1 : (1 : ℝ) ≤ Z := hZ ▸ one_le_pow₀ (by norm_num)
  have rS : (P.S : ℝ) ≤ v := by rw [hv]; exact_mod_cast hSV
  have ra : (P.a : ℝ) ≤ v := by rw [hv]; exact_mod_cast ha'
  have rq : (P.q : ℝ) ≤ v := by rw [hv]; exact_mod_cast hqV
  have rc : (P.c : ℝ) ≤ v := by rw [hv]; exact_mod_cast hcV
  have rR : (P.R : ℝ) ≤ v := by rw [hv]; exact_mod_cast hRV
  have rM : (P.M : ℝ) ≤ v := by rw [hv]; exact_mod_cast hMV
  have rW : (Wb : ℝ) ≤ v := by rw [hv]; exact_mod_cast hWV
  have rm : (m : ℝ) ≤ v := by rw [hv]; exact_mod_cast hmV
  have hlam : feldmanLambdaExponent P ≤ 200 * Z * v ^ 3 := by
    refine le_trans ?_ (lambda_polynomial_le hv1 hZ1)
    unfold feldmanLambdaExponent
    rw [← hZ]
    gcongr
  -- `201 Z v³ ≤ U · U^{5(m+2)²+1} · U^{3(8m+16)} ≤ U^{30(m+2)²}`
  have hZU : Z ≤ (U : ℝ) ^ (5 * (m + 2) ^ 2 + 1) := by
    have : ((2 ^ P.R : ℕ) : ℝ) ≤ ((U ^ (5 * (m + 2) ^ 2 + 1) : ℕ) : ℝ) := by exact_mod_cast h2R
    rw [hZ]; exact_mod_cast this
  have hvU : v ^ 3 = (U : ℝ) ^ (3 * (8 * m + 16)) := by
    rw [hv, hV, Nat.cast_pow, ← pow_mul]; ring_nf
  have hU201 : (201 : ℝ) ≤ U := by
    have : 201 ≤ U := by omega
    exact_mod_cast this
  have hUr1 : (1 : ℝ) ≤ U := by linarith
  have hZv : 1 ≤ Z * v ^ 3 := one_le_mul_of_one_le_of_one_le hZ1 (one_le_pow₀ hv1)
  calc feldmanLambdaExponent P + 1 ≤ 201 * Z * v ^ 3 := by linarith
    _ ≤ (U : ℝ) * (U : ℝ) ^ (5 * (m + 2) ^ 2 + 1) * (U : ℝ) ^ (3 * (8 * m + 16)) := by
        rw [hvU]; gcongr
    _ = (U : ℝ) ^ (1 + (5 * (m + 2) ^ 2 + 1) + 3 * (8 * m + 16)) := by ring
    _ ≤ (U : ℝ) ^ (30 * (m + 2) ^ 2) := pow_le_pow_right₀ hUr1 hexp


/-- **Linear forms in `m + 1` prime logarithms, explicitly.** For distinct primes with
`Σ log p_i ≤ W` and every nonzero `ν`,
`|Σ ν_i log p_i| ≥ exp(−U^{30(m+2)²}(log |ν|₁ + 2))`, `U = 10⁴(W+1)(m+2)²`. -/
theorem abs_primeLogForm_ge_explicit (p : Fin (m + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) {Wb : ℕ} (hW : totalLogSum p ≤ Wb) (ν : Fin (m + 1) → ℤ)
    (hν : ν ≠ 0) :
    Real.exp (-(bakerExponent m Wb * (Real.log (coeffHeight ν) + 2))) ≤ |primeLogForm p ν| := by
  obtain ⟨P, hR, hq, hM, hS, hc, ha⟩ := exists_feldmanParams_of_R m (Wb + 1) (explicitR m (Wb + 1))
    (by omega) (one_le_explicitR _ _) (explicitR_spec _ _)
  have hC := feldmanLambdaExponent_add_one_le (by omega) P hR hq hM hS hc ha
  obtain ⟨k, hk0, hkmax⟩ := exists_max_pivot ν hν
  set σ := Equiv.swap k (Fin.last m) with hσ
  set s : ℤ := if 0 < ν k then 1 else -1 with hs
  have hs1 : |s| = 1 := by rw [hs]; split_ifs <;> simp
  have hsk : s * ν k = |ν k| := by
    rw [hs]
    split_ifs with h
    · rw [one_mul, abs_of_pos h]
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hk0)]; ring
  set b : Fin (m + 1) → ℤ := fun j => s * ν (σ j) with hbdef
  have hblast : b (Fin.last m) = |ν k| := by
    rw [hbdef]; simp only [hσ, Equiv.swap_apply_right]; exact hsk
  have hbpos : 0 < b (Fin.last m) := by rw [hblast]; exact abs_pos.mpr hk0
  have hbmax : ∀ j, |b j| ≤ b (Fin.last m) := by
    intro j
    rw [hblast, hbdef]
    simp only
    rw [abs_mul, hs1, one_mul, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
    exact_mod_cast hkmax (σ j)
  have hp' : Function.Injective (p ∘ σ) := hp.comp σ.injective
  have hprime' : ∀ i, ((p ∘ σ) i).Prime := fun i => hprime (σ i)
  have hW' : totalLogSum (p ∘ σ) ≤ Wb := by rw [totalLogSum_comp_equiv]; exact hW
  have h := feldman_pivot_bound_of_params P (p ∘ σ) hp' hprime' hW' b hbpos hbmax
  have hform : |primeLogForm (p ∘ σ) b| = |primeLogForm p ν| := by
    rw [hbdef, primeLogForm_comp_equiv, abs_mul]
    have : |((s : ℤ) : ℝ)| = 1 := by rw [← Int.cast_abs, hs1, Int.cast_one]
    rw [this, one_mul]
  rw [hform] at h
  refine le_trans ?_ h
  have hx1 : (1 : ℝ) ≤ (b (Fin.last m) : ℝ) := by exact_mod_cast hbpos
  have hxH : ((b (Fin.last m) : ℤ) : ℝ) ≤ (coeffHeight ν : ℝ) := by
    have hle : (ν k).natAbs ≤ coeffHeight ν :=
      single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (mem_univ k)
    rw [hblast, ← Nat.cast_natAbs]
    exact_mod_cast hle
  have hlog : Real.log (b (Fin.last m)) ≤ Real.log (coeffHeight ν) :=
    Real.log_le_log (by linarith) hxH
  have hlog0 : 0 ≤ Real.log (b (Fin.last m)) := Real.log_nonneg hx1
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact mul_le_mul hC (by linarith) (by linarith) (by unfold bakerExponent; positivity)

/-- **Many logarithms of primes up to `y`.** For `m + 1` distinct primes `≤ y` and `ν ≠ 0`,
`|Σ ν_i log p_i| ≥ exp(−U^{30(m+2)²}(log |ν|₁ + 2))` with `U = 10⁴(⌈(m+1) log y⌉ + 1)(m+2)²`;
for `m + 1 ≤ (log y)^A` the exponent is `exp(O((log y)^{2A} log log y))`. -/
theorem abs_primeLogForm_ge_of_le (p : Fin (m + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) {y : ℕ} (hy : ∀ i, p i ≤ y) (ν : Fin (m + 1) → ℤ) (hν : ν ≠ 0) :
    Real.exp (-(bakerExponent m ⌈(m + 1 : ℝ) * Real.log y⌉₊ * (Real.log (coeffHeight ν) + 2))) ≤
      |primeLogForm p ν| := by
  refine abs_primeLogForm_ge_explicit p hp hprime ?_ ν hν
  refine le_trans ?_ (Nat.le_ceil _)
  unfold totalLogSum
  calc ∑ j, Real.log (p j) ≤ ∑ _j : Fin (m + 1), Real.log y :=
        sum_le_sum fun j _ => Real.log_le_log (by exact_mod_cast (hprime j).pos)
          (by exact_mod_cast hy j)
    _ = (m + 1 : ℝ) * Real.log y := by simp

/-! ## Necessity: the exponent grows at least linearly -/

/-- Equal clamped floors of two points of `[0, N]` force distance at most `1`. -/
theorem abs_sub_le_one_of_min_floor_eq {N : ℕ} (hN : 1 ≤ N) {a b : ℝ} (ha0 : 0 ≤ a)
    (haN : a ≤ N) (hb0 : 0 ≤ b) (hbN : b ≤ N)
    (h : min ⌊a⌋₊ (N - 1) = min ⌊b⌋₊ (N - 1)) : |a - b| ≤ 1 := by
  have fa := Nat.floor_le ha0
  have fa' := Nat.lt_floor_add_one a
  have fb := Nat.floor_le hb0
  have fb' := Nat.lt_floor_add_one b
  have hN1 : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub hN]; simp
  rcases le_total ⌊a⌋₊ (N - 1) with h1 | h1 <;> rcases le_total ⌊b⌋₊ (N - 1) with h2 | h2
  · rw [min_eq_left h1, min_eq_left h2] at h
    have : (⌊a⌋₊ : ℝ) = ⌊b⌋₊ := by exact_mod_cast h
    rw [abs_le]; constructor <;> linarith
  · rw [min_eq_left h1, min_eq_right h2] at h
    have hb1 : ((N - 1 : ℕ) : ℝ) ≤ ⌊b⌋₊ := by exact_mod_cast h2
    have : (⌊a⌋₊ : ℝ) = ((N - 1 : ℕ) : ℝ) := by exact_mod_cast h
    rw [abs_le]; constructor <;> linarith
  · rw [min_eq_right h1, min_eq_left h2] at h
    have ha1 : ((N - 1 : ℕ) : ℝ) ≤ ⌊a⌋₊ := by exact_mod_cast h1
    have : (⌊b⌋₊ : ℝ) = ((N - 1 : ℕ) : ℝ) := by exact_mod_cast h.symm
    rw [abs_le]; constructor <;> linarith
  · have ha1 : ((N - 1 : ℕ) : ℝ) ≤ ⌊a⌋₊ := by exact_mod_cast h1
    have hb1 : ((N - 1 : ℕ) : ℝ) ≤ ⌊b⌋₊ := by exact_mod_cast h2
    rw [abs_le]; constructor <;> linarith

/-- **Dirichlet's pigeonhole for linear forms.** For `d ≥ 1` positive integers `p_i` and `H ≥ 1`
there is `ν ≠ 0` with `|ν_i| ≤ H` and `|Σ ν_i log p_i| ((H+1)^d − 1) ≤ H Σ log p_i`. -/
theorem exists_small_primeLogForm {d : ℕ} (p : Fin d → ℕ) (hp : ∀ i, 1 ≤ p i) (hd : 1 ≤ d)
    {H : ℕ} (hH : 1 ≤ H) :
    ∃ ν : Fin d → ℤ, ν ≠ 0 ∧ (∀ i, |ν i| ≤ H) ∧
      |primeLogForm p ν| * (((H + 1) ^ d - 1 : ℕ) : ℝ) ≤ H * ∑ i, Real.log (p i) := by
  classical
  set W := ∑ i, Real.log (p i) with hWdef
  have hlog : ∀ i, 0 ≤ Real.log (p i) := fun i => Real.log_nonneg (by exact_mod_cast hp i)
  have hW0 : 0 ≤ W := sum_nonneg fun i _ => hlog i
  set N := (H + 1) ^ d - 1 with hNdef
  have hpow : 2 ≤ (H + 1) ^ d := by
    calc 2 ≤ (H + 1) ^ 1 := by rw [pow_one]; omega
      _ ≤ (H + 1) ^ d := Nat.pow_le_pow_right (by omega) hd
  have hN1 : 1 ≤ N := by omega
  let f : (Fin d → Fin (H + 1)) → ℝ := fun v => ∑ i, ((v i : ℕ) : ℝ) * Real.log (p i)
  have hf0 : ∀ v, 0 ≤ f v := fun v => sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hlog i)
  have hfH : ∀ v, f v ≤ H * W := fun v => by
    simp only [f, hWdef, mul_sum]
    refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (hlog i)
    exact_mod_cast Nat.lt_succ_iff.mp (v i).isLt
  let g : (Fin d → Fin (H + 1)) → ℕ := fun v => min ⌊f v * N / (H * W)⌋₊ (N - 1)
  have hmaps : ∀ v ∈ (univ : Finset (Fin d → Fin (H + 1))), g v ∈ range N := fun v _ => by
    simp only [g, mem_range]; omega
  have hcard : (range N).card < (univ : Finset (Fin d → Fin (H + 1))).card := by
    simp only [card_range, card_univ, Fintype.card_fun, Fintype.card_fin]; omega
  obtain ⟨v, -, w, -, hvw, hg⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  refine ⟨fun i => ((v i : ℕ) : ℤ) - ((w i : ℕ) : ℤ), ?_, fun i => ?_, ?_⟩
  · intro h0
    apply hvw
    funext i
    have := congrFun h0 i
    simp only [Pi.zero_apply, sub_eq_zero] at this
    exact Fin.ext (by exact_mod_cast this)
  · have h1 := (v i).isLt
    have h2 := (w i).isLt
    rw [abs_le]; constructor <;> push_cast <;> omega
  · have hform : primeLogForm p (fun i => ((v i : ℕ) : ℤ) - ((w i : ℕ) : ℤ)) = f v - f w := by
      simp only [primeLogForm, f, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      push_cast; ring
    rw [hform]
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    rcases eq_or_lt_of_le (mul_nonneg (Nat.cast_nonneg H : (0 : ℝ) ≤ H) hW0) with hHW | hHW
    · have hv0 : f v = 0 := le_antisymm (by linarith [hfH v]) (hf0 v)
      have hw0 : f w = 0 := le_antisymm (by linarith [hfH w]) (hf0 w)
      rw [hv0, hw0]; simp; linarith
    · have hav := hf0 v; have haw := hf0 w
      have hNpos : (0 : ℝ) < N := by linarith
      have key := abs_sub_le_one_of_min_floor_eq hN1
        (div_nonneg (mul_nonneg hav hNpos.le) hHW.le)
        ((div_le_iff₀ hHW).mpr (by nlinarith [hfH v]))
        (div_nonneg (mul_nonneg haw hNpos.le) hHW.le)
        ((div_le_iff₀ hHW).mpr (by nlinarith [hfH w])) hg
      rw [← sub_div, ← sub_mul, abs_div, abs_of_pos hHW, abs_mul, abs_of_pos hNpos,
        div_le_one hHW] at key
      linarith

/-- **No exponent below `d − 1`.** If `c(2 + |ν|₁)^{−C} ≤ |Σ ν_i log p_i|` for every nonzero `ν`,
`d ≥ 2`, then `C ≥ d − 1`. -/
theorem le_exponent_of_bakerBound {d : ℕ} (hd : 2 ≤ d) (p : Fin d → ℕ) (hp : ∀ i, 1 ≤ p i)
    {c C : ℝ} (hc : 0 < c)
    (hbound : ∀ ν : Fin d → ℤ, ν ≠ 0 → c * (2 + (coeffHeight ν : ℝ)) ^ (-C) ≤ |primeLogForm p ν|) :
    (d : ℝ) - 1 ≤ C := by
  by_contra hC
  push Not at hC
  set C' := max C 0 with hC'
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hC'lt : C' < (d : ℝ) - 1 := max_lt hC (by linarith)
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set e := (d : ℝ) - 1 - C' with he
  have he0 : 0 < e := by linarith
  set W := ∑ i, Real.log (p i) with hWdef
  have hW0 : 0 ≤ W := sum_nonneg fun i _ => Real.log_nonneg (by exact_mod_cast hp i)
  have hd0 : (0 : ℝ) < d := by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                               linarith
  set K := W * (3 * d) ^ C' / c with hK
  have hK0 : 0 ≤ K := by positivity
  -- a height `H` with `H^e > K`
  obtain ⟨H, hH1, hHK⟩ : ∃ H : ℕ, 1 ≤ H ∧ K < (H : ℝ) ^ e := by
    refine ⟨⌈K ^ (1 / e)⌉₊ + 1, by omega, ?_⟩
    have h1 : K ^ (1 / e) < (⌈K ^ (1 / e)⌉₊ + 1 : ℕ) := by
      push_cast; exact (Nat.le_ceil _).trans_lt (lt_add_one _)
    calc K = (K ^ (1 / e)) ^ e := by
          rw [← Real.rpow_mul hK0, one_div_mul_cancel he0.ne', Real.rpow_one]
      _ < _ := Real.rpow_lt_rpow (by positivity) h1 he0
  obtain ⟨ν, hν0, hνH, hsmall⟩ := exists_small_primeLogForm p hp (by omega) hH1
  have hlow := hbound ν hν0
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast hH1
  have hH0 : (0 : ℝ) < H := by linarith
  -- `|ν|₁ ≤ dH`, so `2 + |ν|₁ ≤ 3dH`
  have hht : (coeffHeight ν : ℝ) ≤ d * H := by
    have : coeffHeight ν ≤ d * H := by
      unfold coeffHeight
      calc ∑ i, (ν i).natAbs ≤ ∑ _i : Fin d, H := sum_le_sum fun i _ => by
            have := abs_le.mp (hνH i); omega
        _ = d * H := by simp
    exact_mod_cast this
  have hbase : 2 + (coeffHeight ν : ℝ) ≤ 3 * d * H := by nlinarith
  have hbase0 : (0 : ℝ) < 2 + (coeffHeight ν : ℝ) := by positivity
  have hlow' : c * (3 * d * H) ^ (-C') ≤ |primeLogForm p ν| := by
    refine le_trans ?_ hlow
    rcases le_total 0 C with hC0 | hC0
    · rw [hC', max_eq_left hC0]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hbase0 hbase (by linarith)) hc.le
    · rw [hC', max_eq_right hC0, neg_zero, Real.rpow_zero, mul_one]
      have : (1 : ℝ) ≤ (2 + (coeffHeight ν : ℝ)) ^ (-C) :=
        Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) (coeffHeight ν)]) (by linarith)
      nlinarith
  -- `|Λ| H^{d−1} ≤ W`
  have hNH : (H : ℝ) ^ d ≤ (((H + 1) ^ d - 1 : ℕ) : ℝ) := by
    have h1 : H ^ d < (H + 1) ^ d := Nat.pow_lt_pow_left (by omega) (by omega)
    have : H ^ d ≤ (H + 1) ^ d - 1 := by omega
    exact_mod_cast this
  have hup : |primeLogForm p ν| * (H : ℝ) ^ (d - 1) ≤ W := by
    have h1 : |primeLogForm p ν| * (H : ℝ) ^ d ≤ H * W :=
      (mul_le_mul_of_nonneg_left hNH (abs_nonneg _)).trans hsmall
    have hHd : (H : ℝ) ^ d = H * (H : ℝ) ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hHd] at h1
    have h2 : (H : ℝ) * (|primeLogForm p ν| * (H : ℝ) ^ (d - 1)) ≤ H * W := by linarith
    exact le_of_mul_le_mul_left h2 hH0
  -- `c (3d)^{−C'} H^e ≤ W`
  have hsplit : (3 * d * H : ℝ) ^ (-C') = (3 * d : ℝ) ^ (-C') * (H : ℝ) ^ (-C') :=
    Real.mul_rpow (by positivity) hH0.le
  have hHe : (H : ℝ) ^ (-C') * (H : ℝ) ^ (d - 1) = (H : ℝ) ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hH0, Nat.cast_sub (by omega : 1 ≤ d)]
    congr 1; push_cast; rw [he]; ring
  have hkey : c * (3 * d : ℝ) ^ (-C') * (H : ℝ) ^ e ≤ W := by
    calc c * (3 * d : ℝ) ^ (-C') * (H : ℝ) ^ e
        = c * (3 * d * H : ℝ) ^ (-C') * (H : ℝ) ^ (d - 1) := by
          rw [hsplit, ← hHe]; ring
      _ ≤ |primeLogForm p ν| * (H : ℝ) ^ (d - 1) :=
          mul_le_mul_of_nonneg_right hlow' (by positivity)
      _ ≤ W := hup
  have hpos : 0 < c * (3 * d : ℝ) ^ (-C') := by positivity
  have hle : (H : ℝ) ^ e ≤ K := by
    rw [hK, le_div_iff₀ hc]
    have h3 : (0 : ℝ) < (3 * d : ℝ) ^ C' := by positivity
    have hinv : (3 * d : ℝ) ^ (-C') = ((3 * d : ℝ) ^ C')⁻¹ := Real.rpow_neg (by positivity) _
    rw [hinv] at hkey
    have h4 := mul_le_mul_of_nonneg_right hkey h3.le
    calc (H : ℝ) ^ e * c = c * ((3 * d : ℝ) ^ C')⁻¹ * (H : ℝ) ^ e * (3 * d : ℝ) ^ C' := by
          field_simp
      _ ≤ W * (3 * d : ℝ) ^ C' := h4
  linarith

end

end GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit
