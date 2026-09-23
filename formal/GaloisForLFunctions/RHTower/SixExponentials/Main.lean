import GaloisForLFunctions.RHTower.SixExponentials.Extrapolation
import GaloisForLFunctions.RHTower.BakerProof.BakerIteration

/-!
# The six exponentials theorem

For `x₀, x₁` rationally independent and `y₀, y₁, y₂` rationally independent, at least one of the
six numbers `exp(x_i y_j)` is transcendental.

The proof assembles the modules of this folder.  With `d = [K:ℚ]`, `N` large, `M₀ = N²`,
`L = 2 d N³`, Siegel's lemma gives coefficients vanishing at the level-`M₀` samples.  If the
auxiliary function vanishes at all samples of level `M ≥ M₀`, the Schwarz step bounds it at
every sample of level `M + 1` by `(2/3)^{M³} L² B exp(4LXY(M+1))`, while the Liouville step
bounds a nonzero value below by `(H^{6L(M+1)} (L² H^{6L(M+1)} B)^{d−1})⁻¹`; the parameter
inequality `M³ log(3/2) > K₁ + K₂ N³ M` makes the two incompatible, so the function vanishes at
level `M + 1`.  By induction it vanishes at every level, hence, by the Schwarz step on discs of
growing radius, everywhere, contradicting the nonvanishing of an exponential polynomial with
distinct frequencies and nonzero coefficients.

Corollary: for a nonreal `ρ` and three distinct primes `p, q, r`, not all of `p^ρ, q^ρ, r^ρ` are
algebraic.
-/

open Complex Finset NumberField

namespace GaloisForLFunctions.RHTower.SixExponentials

/-! ### Real parameter lemmas -/

theorem log_three_halves_pos : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)

theorem log_two_thirds : Real.log (2 / 3) = -Real.log (3 / 2) := by
  rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]

/-- `(2/3)^{n³} · P · exp c < ε` follows from `log P + c < n³ log(3/2) + log ε`. -/
theorem two_thirds_pow_mul_lt {n : ℕ} {P c ε : ℝ} (hP : 0 < P) (hε : 0 < ε)
    (h : Real.log P + c < (n : ℝ) ^ (3 : ℕ) * Real.log (3 / 2) + Real.log ε) :
    (2 / 3 : ℝ) ^ (n ^ (3 : ℕ)) * (P * Real.exp c) < ε := by
  have h23 : (0 : ℝ) < 2 / 3 := by norm_num
  have e1 : (2 / 3 : ℝ) ^ (n ^ (3 : ℕ)) = Real.exp (((n ^ (3 : ℕ) : ℕ) : ℝ) * Real.log (2 / 3)) := by
    rw [Real.exp_nat_mul, Real.exp_log h23]
  have e2 : P = Real.exp (Real.log P) := (Real.exp_log hP).symm
  rw [e1]
  conv_lhs => rw [e2]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_log hε, Real.exp_lt_exp, log_two_thirds]
  push_cast
  linarith

/-- For `N` large and `M ≥ N²`, `K₁ + K₂ N³ M < M³ log(3/2)`. -/
theorem exists_parameter {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ M : ℕ, N₀ ^ (2 : ℕ) ≤ M →
      K₁ + K₂ * ((N₀ : ℝ) ^ (3 : ℕ) * M) < (M : ℝ) ^ (3 : ℕ) * Real.log (3 / 2) := by
  have hlog := log_three_halves_pos
  refine ⟨⌈(K₁ + 1 + K₂) / Real.log (3 / 2)⌉₊ + 1, by omega, ?_⟩
  intro M hM
  set N : ℕ := ⌈(K₁ + 1 + K₂) / Real.log (3 / 2)⌉₊ + 1 with hNdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNlog : K₁ + 1 + K₂ ≤ N * Real.log (3 / 2) := by
    have h1 : (K₁ + 1 + K₂) / Real.log (3 / 2) ≤ N := by
      calc (K₁ + 1 + K₂) / Real.log (3 / 2) ≤ ⌈(K₁ + 1 + K₂) / Real.log (3 / 2)⌉₊ :=
            Nat.le_ceil _
        _ ≤ N := by
            rw [hNdef]
            push_cast
            linarith
    rwa [div_le_iff₀ hlog] at h1
  have hMr : (N : ℝ) ^ (2 : ℕ) ≤ M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by nlinarith
  have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ (3 : ℕ) := one_le_pow₀ hN1
  set T : ℝ := (N : ℝ) ^ (3 : ℕ) * M with hT
  have hT1 : 1 ≤ T := by
    rw [hT]
    nlinarith
  have hM3 : (N : ℝ) * T ≤ (M : ℝ) ^ (3 : ℕ) := by
    rw [hT]
    have h4 : (N : ℝ) ^ (4 : ℕ) ≤ (M : ℝ) ^ (2 : ℕ) := by
      calc (N : ℝ) ^ (4 : ℕ) = ((N : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
        _ ≤ (M : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ (by positivity) hMr 2
    calc (N : ℝ) * ((N : ℝ) ^ (3 : ℕ) * M) = (N : ℝ) ^ (4 : ℕ) * M := by ring
      _ ≤ (M : ℝ) ^ (2 : ℕ) * M := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = (M : ℝ) ^ (3 : ℕ) := by ring
  calc K₁ + K₂ * T < K₁ * T + T + K₂ * T := by nlinarith [mul_nonneg hK₁ (sub_nonneg.mpr hT1)]
    _ = (K₁ + 1 + K₂) * T := by ring
    _ ≤ (N * Real.log (3 / 2)) * T := mul_le_mul_of_nonneg_right hNlog (by linarith)
    _ = Real.log (3 / 2) * (N * T) := by ring
    _ ≤ Real.log (3 / 2) * (M : ℝ) ^ (3 : ℕ) := mul_le_mul_of_nonneg_left hM3 hlog.le
    _ = (M : ℝ) ^ (3 : ℕ) * Real.log (3 / 2) := by ring

/-- For `M` large, `a + b (M + 1) < M³ log(3/2)`. -/
theorem exists_M_large (a b : ℝ) : ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M →
    a + b * ((M : ℝ) + 1) < (M : ℝ) ^ (3 : ℕ) * Real.log (3 / 2) := by
  have hlog := log_three_halves_pos
  refine ⟨⌈(|a| + 2 * |b| + 1) / Real.log (3 / 2)⌉₊ + 1, ?_⟩
  intro M hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hMlog : |a| + 2 * |b| + 1 ≤ M * Real.log (3 / 2) := by
    have h1 : (|a| + 2 * |b| + 1) / Real.log (3 / 2) ≤ M := by
      calc (|a| + 2 * |b| + 1) / Real.log (3 / 2)
          ≤ ⌈(|a| + 2 * |b| + 1) / Real.log (3 / 2)⌉₊ := Nat.le_ceil _
        _ ≤ M := by exact_mod_cast (by omega : ⌈(|a| + 2 * |b| + 1) / Real.log (3 / 2)⌉₊ ≤ M)
    rwa [div_le_iff₀ hlog] at h1
  have ha := le_abs_self a
  have hb := le_abs_self b
  have hb' : b * ((M : ℝ) + 1) ≤ |b| * ((M : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hb (by linarith)
  have habs0 : 0 ≤ |b| := abs_nonneg b
  have hab : 0 ≤ |a| * ((M : ℝ) - 1) := mul_nonneg (abs_nonneg a) (by linarith)
  have hbb : 0 ≤ |b| * ((M : ℝ) - 1) := mul_nonneg habs0 (by linarith)
  have hM23 : (M : ℝ) ^ (2 : ℕ) ≤ (M : ℝ) ^ (3 : ℕ) := by
    have : 0 ≤ (M : ℝ) ^ (2 : ℕ) * ((M : ℝ) - 1) := mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  calc a + b * ((M : ℝ) + 1) ≤ |a| + |b| * ((M : ℝ) + 1) := by linarith
    _ < (|a| + 2 * |b| + 1) * M := by nlinarith
    _ ≤ (M * Real.log (3 / 2)) * M := mul_le_mul_of_nonneg_right hMlog (by linarith)
    _ = (M : ℝ) ^ (2 : ℕ) * Real.log (3 / 2) := by ring
    _ ≤ (M : ℝ) ^ (3 : ℕ) * Real.log (3 / 2) := mul_le_mul_of_nonneg_right hM23 hlog.le

/-- **The key parameter inequality in multiplicative form.**  With `L = 2 d N³`, `M ≥ N²`, and
the Siegel bound on `B`, the product of the Schwarz and Liouville factors is below one. -/
theorem final_lt_one {d L N M : ℕ} {c₁ H X Y B : ℝ} (hd : 1 ≤ d) (hc₁ : 1 ≤ c₁) (hH : 1 ≤ H)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hL : L = 2 * d * N ^ (3 : ℕ)) (hN : 1 ≤ N) (hM : N ^ (2 : ℕ) ≤ M)
    (hB1 : 1 ≤ B) (hB : B ≤ 2 * c₁ ^ (2 : ℕ) * ((L : ℝ) * L) * H ^ (6 * L * N ^ (2 : ℕ)))
    (hpar : (d * Real.log (2 * c₁ ^ (2 : ℕ)) + 2 * d * Real.log (4 * (d : ℝ) ^ (2 : ℕ)))
      + (12 * d + 36 * (d : ℝ) ^ (2 : ℕ) * Real.log H + 16 * d * X * Y) * ((N : ℝ) ^ (3 : ℕ) * M)
      < (M : ℝ) ^ (3 : ℕ) * Real.log (3 / 2)) :
    (2 / 3 : ℝ) ^ (M ^ (3 : ℕ)) * ((((L : ℝ) * L) * B) ^ d * H ^ (6 * L * (M + 1) * d)
      * Real.exp (4 * L * X * Y * (M + 1))) < 1 := by
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hHpos : 0 < H := by linarith
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := by linarith
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hMr : (N : ℝ) ^ (2 : ℕ) ≤ M := by exact_mod_cast hM
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := one_le_pow₀ hNr
  have hM1 : (1 : ℝ) ≤ M := le_trans hN2 hMr
  have hLr : (L : ℝ) = 2 * d * (N : ℝ) ^ (3 : ℕ) := by rw [hL]; push_cast; ring
  have hLL : (L : ℝ) * L = 4 * (d : ℝ) ^ (2 : ℕ) * (N : ℝ) ^ (6 : ℕ) := by rw [hLr]; ring
  have hLLpos : (0 : ℝ) < (L : ℝ) * L := by rw [hLL]; positivity
  have hQpos : 0 < (L : ℝ) * L * B := mul_pos hLLpos (by linarith)
  have hP : 0 < ((L : ℝ) * L * B) ^ d * H ^ (6 * L * (M + 1) * d) :=
    mul_pos (pow_pos hQpos d) (pow_pos hHpos _)
  apply two_thirds_pow_mul_lt hP one_pos
  rw [Real.log_one, add_zero, Real.log_mul (pow_pos hQpos d).ne' (pow_pos hHpos _).ne',
    Real.log_pow, Real.log_pow, Real.log_mul hLLpos.ne' (by linarith)]
  have hlogB : Real.log B ≤ Real.log (2 * c₁ ^ (2 : ℕ)) + Real.log ((L : ℝ) * L)
      + ((6 * L * N ^ (2 : ℕ) : ℕ) : ℝ) * Real.log H := by
    calc Real.log B ≤ Real.log (2 * c₁ ^ (2 : ℕ) * ((L : ℝ) * L) * H ^ (6 * L * N ^ (2 : ℕ))) :=
          Real.log_le_log (by linarith) hB
      _ = Real.log (2 * c₁ ^ (2 : ℕ)) + Real.log ((L : ℝ) * L)
          + ((6 * L * N ^ (2 : ℕ) : ℕ) : ℝ) * Real.log H := by
          rw [Real.log_mul (by positivity) (pow_pos hHpos _).ne',
            Real.log_mul (by positivity) hLLpos.ne', Real.log_pow]
  have hlogLL : Real.log ((L : ℝ) * L) ≤ Real.log (4 * (d : ℝ) ^ (2 : ℕ)) + 6 * N := by
    rw [hLL, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N)
    push_cast
    linarith
  set S : ℝ := (N : ℝ) ^ (3 : ℕ) * M with hS
  have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ (3 : ℕ) := one_le_pow₀ hNr
  have hS1 : (N : ℝ) ≤ S := by
    rw [hS]
    have h1 : (N : ℝ) ≤ (N : ℝ) ^ (3 : ℕ) := by
      calc (N : ℝ) = N * 1 := by ring
        _ ≤ N * (N : ℝ) ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hN2 (by linarith)
        _ = (N : ℝ) ^ (3 : ℕ) := by ring
    calc (N : ℝ) ≤ (N : ℝ) ^ (3 : ℕ) := h1
      _ = (N : ℝ) ^ (3 : ℕ) * 1 := by ring
      _ ≤ (N : ℝ) ^ (3 : ℕ) * M := mul_le_mul_of_nonneg_left hM1 (by linarith)
  have hS5 : (N : ℝ) ^ (5 : ℕ) ≤ S := by
    rw [hS]
    calc (N : ℝ) ^ (5 : ℕ) = (N : ℝ) ^ (3 : ℕ) * (N : ℝ) ^ (2 : ℕ) := by ring
      _ ≤ (N : ℝ) ^ (3 : ℕ) * M := mul_le_mul_of_nonneg_left hMr (by linarith)
  have hS3 : (N : ℝ) ^ (3 : ℕ) * ((M : ℝ) + 1) ≤ 2 * S := by
    rw [hS]
    have : (M : ℝ) + 1 ≤ 2 * M := by linarith
    calc (N : ℝ) ^ (3 : ℕ) * ((M : ℝ) + 1) ≤ (N : ℝ) ^ (3 : ℕ) * (2 * M) :=
          mul_le_mul_of_nonneg_left this (by linarith)
      _ = 2 * ((N : ℝ) ^ (3 : ℕ) * M) := by ring
  have hpos1 : 0 ≤ Real.log (2 * c₁ ^ (2 : ℕ)) := Real.log_nonneg (by nlinarith)
  have hpos2 : 0 ≤ Real.log (4 * (d : ℝ) ^ (2 : ℕ)) := Real.log_nonneg (by nlinarith)
  have e1 : ((6 * L * N ^ (2 : ℕ) : ℕ) : ℝ) * Real.log H = 12 * (d : ℝ) * (N : ℝ) ^ (5 : ℕ) * Real.log H := by
    push_cast
    rw [hLr]
    ring
  have e2 : ((6 * L * (M + 1) * d : ℕ) : ℝ) * Real.log H
      = 12 * (d : ℝ) ^ (2 : ℕ) * Real.log H * ((N : ℝ) ^ (3 : ℕ) * ((M : ℝ) + 1)) := by
    push_cast
    rw [hLr]
    ring
  have e3 : 4 * (L : ℝ) * X * Y * ((M : ℝ) + 1)
      = 8 * (d : ℝ) * X * Y * ((N : ℝ) ^ (3 : ℕ) * ((M : ℝ) + 1)) := by
    rw [hLr]
    ring
  have hXY : 0 ≤ X * Y := mul_nonneg hX hY
  have hc2 : 0 ≤ 12 * (d : ℝ) ^ (2 : ℕ) * Real.log H := mul_nonneg (by positivity) hlogH
  have hc3 : 0 ≤ 8 * (d : ℝ) * X * Y := mul_nonneg (mul_nonneg (by positivity) hX) hY
  have t1 : (d : ℝ) * Real.log B ≤ d * Real.log (2 * c₁ ^ (2 : ℕ)) + d * Real.log ((L : ℝ) * L)
      + 12 * (d : ℝ) ^ (2 : ℕ) * Real.log H * (N : ℝ) ^ (5 : ℕ) := by
    calc (d : ℝ) * Real.log B ≤ d * (Real.log (2 * c₁ ^ (2 : ℕ)) + Real.log ((L : ℝ) * L)
          + ((6 * L * N ^ (2 : ℕ) : ℕ) : ℝ) * Real.log H) := mul_le_mul_of_nonneg_left hlogB hd0
      _ = d * Real.log (2 * c₁ ^ (2 : ℕ)) + d * Real.log ((L : ℝ) * L)
          + 12 * (d : ℝ) ^ (2 : ℕ) * Real.log H * (N : ℝ) ^ (5 : ℕ) := by
          rw [e1]
          ring
  have t2 : (d : ℝ) * Real.log ((L : ℝ) * L) ≤ d * Real.log (4 * (d : ℝ) ^ (2 : ℕ)) + 6 * d * N := by
    calc (d : ℝ) * Real.log ((L : ℝ) * L) ≤ d * (Real.log (4 * (d : ℝ) ^ (2 : ℕ)) + 6 * N) :=
          mul_le_mul_of_nonneg_left hlogLL hd0
      _ = d * Real.log (4 * (d : ℝ) ^ (2 : ℕ)) + 6 * d * N := by ring
  have t3 : 12 * (d : ℝ) ^ (2 : ℕ) * Real.log H * (N : ℝ) ^ (5 : ℕ) ≤ 12 * (d : ℝ) ^ (2 : ℕ) * Real.log H * S :=
    mul_le_mul_of_nonneg_left hS5 hc2
  have t4 : 12 * (d : ℝ) ^ (2 : ℕ) * Real.log H * ((N : ℝ) ^ (3 : ℕ) * ((M : ℝ) + 1))
      ≤ 12 * (d : ℝ) ^ (2 : ℕ) * Real.log H * (2 * S) := mul_le_mul_of_nonneg_left hS3 hc2
  have t5 : 8 * (d : ℝ) * X * Y * ((N : ℝ) ^ (3 : ℕ) * ((M : ℝ) + 1))
      ≤ 8 * (d : ℝ) * X * Y * (2 * S) := mul_le_mul_of_nonneg_left hS3 hc3
  have t6 : 6 * (d : ℝ) * N ≤ 6 * (d : ℝ) * S := mul_le_mul_of_nonneg_left hS1 (by positivity)
  have hpar2 : (12 * d + 36 * (d : ℝ) ^ (2 : ℕ) * Real.log H + 16 * d * X * Y) * S
      = 12 * d * S + 36 * (d : ℝ) ^ (2 : ℕ) * Real.log H * S + 16 * d * X * Y * S := by ring
  rw [hpar2] at hpar
  rw [e2, e3, mul_add]
  linarith [t1, t2, t3, t4, t5, t6, hpar]

/-- The three inequalities of one induction step are contradictory. -/
theorem combine_step {d : ℕ} (hd : 1 ≤ d) {F a Q E t : ℝ} (ha : 0 ≤ a) (hQ : 0 ≤ Q)
    (hup : F ≤ t * (Q * E)) (hlow : 1 ≤ a * F * (Q * a) ^ (d - 1))
    (hfin : t * (Q ^ d * a ^ d * E) < 1) : False := by
  have hF0 : 0 ≤ F := by
    by_contra h
    push Not at h
    have : a * F * (Q * a) ^ (d - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos ha h.le) (by positivity)
    linarith
  have hprod : (Q * a) ^ (d - 1) * (Q * a) = (Q * a) ^ d := pow_sub_one_mul (by omega) _
  have hkey : (1 : ℝ) ≤ t * (Q ^ d * a ^ d * E) := by
    calc (1 : ℝ) ≤ a * F * (Q * a) ^ (d - 1) := hlow
      _ ≤ a * (t * (Q * E)) * (Q * a) ^ (d - 1) := by gcongr
      _ = t * E * ((Q * a) ^ (d - 1) * (Q * a)) := by ring
      _ = t * E * (Q * a) ^ d := by rw [hprod]
      _ = t * (Q ^ d * a ^ d * E) := by rw [mul_pow]; ring
  linarith

/-! ### The theorem -/

/-- **Six exponentials, structured form.**  The data cannot have all six exponentials
algebraic. -/
theorem AlgData.false (A : AlgData) : False := by
  classical
  have hd1 : 1 ≤ Module.finrank ℚ A.K := Module.finrank_pos
  set d := Module.finrank ℚ A.K with hd
  have hc₁ := one_le_siegel_c₁ A.K
  set c₁ := GelfondSchneiderSiegel.c₁ A.K with hc₁def
  have hH1 := A.one_le_Hb
  have hH0 : 0 ≤ A.Hb := le_trans zero_le_one hH1
  have hX0 := A.toData.X_nonneg
  have hY0 := A.toData.Y_pos
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hK₁ : 0 ≤ d * Real.log (2 * c₁ ^ (2 : ℕ)) + 2 * d * Real.log (4 * (d : ℝ) ^ (2 : ℕ)) := by
    have h1 : 0 ≤ Real.log (2 * c₁ ^ (2 : ℕ)) := Real.log_nonneg (by nlinarith)
    have h2 : 0 ≤ Real.log (4 * (d : ℝ) ^ (2 : ℕ)) := Real.log_nonneg (by nlinarith)
    positivity
  have hK₂ : 0 ≤ 12 * d + 36 * (d : ℝ) ^ (2 : ℕ) * Real.log A.Hb
      + 16 * d * A.toData.X * A.toData.Y := by
    have := Real.log_nonneg hH1
    positivity
  obtain ⟨N, hN1, hpar⟩ := exists_parameter hK₁ hK₂
  set L := 2 * d * N ^ (3 : ℕ) with hL
  set M₀ := N ^ (2 : ℕ) with hM₀
  have hLpos : 0 < L := by positivity
  have hM₀pos : 0 < M₀ := by positivity
  have h2 : 2 * M₀ ^ (3 : ℕ) ≤ L * L := by
    rw [hL, hM₀]
    have hdd : 1 ≤ d * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc 2 * (N ^ (2 : ℕ)) ^ (3 : ℕ) = 2 * N ^ (6 : ℕ) := by ring
      _ ≤ (4 * (d * d)) * N ^ (6 : ℕ) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * d * N ^ (3 : ℕ) * (2 * d * N ^ (3 : ℕ)) := by ring
  obtain ⟨ξ, B, hξ, hker, hB1, hB, hBle⟩ := A.exists_coefficients hLpos hM₀pos h2
  have hB0 : 0 ≤ B := by linarith
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  -- vanishing at every level `M₀ + k`
  have hvan : ∀ k : ℕ, ∀ m : Fin 3 → Fin (M₀ + k), A.F ξ (A.toData.pt m) = 0 := by
    intro k
    induction k with
    | zero =>
      intro m
      exact A.F_pt_eq_zero_of_ker ξ hker m
    | succ k ih =>
      intro m
      by_contra hne
      have hMge : N ^ (2 : ℕ) ≤ M₀ + k := by omega
      have hz : ‖A.toData.pt m‖ ≤ ((M₀ + k : ℕ) + 1) * A.toData.Y := by
        have := A.toData.norm_pt_le m
        push_cast at this ⊢
        linarith
      have hup := A.norm_F_le_of_vanishing ξ hB hB0 ih hz
      have hlow := A.one_le_of_F_ne_zero ξ hB hB0 m hne
      have hpar' := hpar (M₀ + k) hMge
      have hfin := final_lt_one hd1 hc₁ hH1 hX0 hY0.le hL hN1 hMge hB1 hBle hpar'
      have hexp : Real.exp (L * A.toData.X * (4 * (((M₀ + k : ℕ) : ℝ) + 1) * A.toData.Y))
          = Real.exp (4 * L * A.toData.X * A.toData.Y * (((M₀ + k : ℕ) : ℝ) + 1)) := by
        congr 1
        ring
      have hup' : ‖A.F ξ (A.toData.pt m)‖ ≤ (2 / 3 : ℝ) ^ ((M₀ + k) ^ (3 : ℕ))
          * (((L : ℝ) * L * B) * Real.exp (4 * L * A.toData.X * A.toData.Y
            * (((M₀ + k : ℕ) : ℝ) + 1))) := by
        calc ‖A.F ξ (A.toData.pt m)‖ ≤ _ := hup
          _ = _ := by rw [hexp]; ring
      have hapow : (A.Hb ^ (6 * L * (M₀ + (k + 1)))) ^ d = A.Hb ^ (6 * L * (M₀ + k + 1) * d) := by
        rw [← pow_mul]
        congr 1
      have hlow' : (1 : ℝ) ≤ A.Hb ^ (6 * L * (M₀ + (k + 1))) * ‖A.F ξ (A.toData.pt m)‖
          * (((L : ℝ) * L * B) * A.Hb ^ (6 * L * (M₀ + (k + 1)))) ^ (d - 1) := by
        calc (1 : ℝ) ≤ _ := hlow
          _ = _ := by ring
      have hfin' : (2 / 3 : ℝ) ^ ((M₀ + k) ^ (3 : ℕ)) * (((L : ℝ) * L * B) ^ d
          * (A.Hb ^ (6 * L * (M₀ + (k + 1)))) ^ d
          * Real.exp (4 * L * A.toData.X * A.toData.Y * (((M₀ + k : ℕ) : ℝ) + 1))) < 1 := by
        rw [hapow]
        have := hfin
        push_cast at this ⊢
        linarith
      exact combine_step hd1 (pow_nonneg hH0 _) (by positivity) hup' hlow' hfin'
  -- the function vanishes everywhere
  have hall : ∀ z, A.F ξ z = 0 := by
    intro z
    by_contra hz0
    have hε : 0 < ‖A.F ξ z‖ := norm_pos_iff.mpr hz0
    obtain ⟨M₁, hM₁⟩ := exists_M_large (Real.log ((L : ℝ) * L * B / ‖A.F ξ z‖))
      (4 * L * A.toData.X * A.toData.Y)
    have hvank := hvan (M₁ + ⌈‖z‖ / A.toData.Y⌉₊)
    have hzle : ‖z‖ ≤ ((M₀ + (M₁ + ⌈‖z‖ / A.toData.Y⌉₊) : ℕ) + 1) * A.toData.Y := by
      have h1 : ‖z‖ / A.toData.Y ≤ ⌈‖z‖ / A.toData.Y⌉₊ := Nat.le_ceil _
      rw [div_le_iff₀ hY0] at h1
      have h2 : (⌈‖z‖ / A.toData.Y⌉₊ : ℝ)
          ≤ ((M₀ + (M₁ + ⌈‖z‖ / A.toData.Y⌉₊) : ℕ) : ℝ) + 1 := by
        push_cast
        have : (0 : ℝ) ≤ M₀ := by positivity
        have : (0 : ℝ) ≤ M₁ := by positivity
        linarith
      calc ‖z‖ ≤ (⌈‖z‖ / A.toData.Y⌉₊ : ℝ) * A.toData.Y := h1
        _ ≤ (((M₀ + (M₁ + ⌈‖z‖ / A.toData.Y⌉₊) : ℕ) : ℝ) + 1) * A.toData.Y :=
            mul_le_mul_of_nonneg_right h2 hY0.le
    have hup := A.norm_F_le_of_vanishing ξ hB hB0 hvank hzle
    have hbig := hM₁ (M₀ + (M₁ + ⌈‖z‖ / A.toData.Y⌉₊)) (by omega)
    have hQpos : 0 < (L : ℝ) * L * B := by positivity
    have hlt : (2 / 3 : ℝ) ^ ((M₀ + (M₁ + ⌈‖z‖ / A.toData.Y⌉₊)) ^ (3 : ℕ))
        * (((L : ℝ) * L * B) * Real.exp (4 * L * A.toData.X * A.toData.Y
          * (((M₀ + (M₁ + ⌈‖z‖ / A.toData.Y⌉₊) : ℕ) : ℝ) + 1)))
        < ‖A.F ξ z‖ := by
      apply two_thirds_pow_mul_lt hQpos hε
      rw [Real.log_div hQpos.ne' hε.ne'] at hbig
      linarith
    have hexp : Real.exp (L * A.toData.X
        * (4 * (((M₀ + (M₁ + ⌈‖z‖ / A.toData.Y⌉₊) : ℕ) : ℝ) + 1) * A.toData.Y))
        = Real.exp (4 * L * A.toData.X * A.toData.Y
          * (((M₀ + (M₁ + ⌈‖z‖ / A.toData.Y⌉₊) : ℕ) : ℝ) + 1)) := by
      congr 1
      ring
    rw [hexp] at hup
    have hup' : ‖A.F ξ z‖ ≤ (2 / 3 : ℝ) ^ ((M₀ + (M₁ + ⌈‖z‖ / A.toData.Y⌉₊)) ^ (3 : ℕ))
        * (((L : ℝ) * L * B) * Real.exp (4 * L * A.toData.X * A.toData.Y
          * (((M₀ + (M₁ + ⌈‖z‖ / A.toData.Y⌉₊) : ℕ) : ℝ) + 1))) := by
      calc ‖A.F ξ z‖ ≤ _ := hup
        _ = _ := by ring
    linarith
  obtain ⟨z, hz⟩ := A.exists_F_ne_zero hLpos ξ hξ
  exact hz (hall z)

/-- **The six exponentials theorem.**  For `x₀, x₁` rationally independent and `y₀, y₁, y₂`
rationally independent, at least one of the six numbers `exp(x_i y_j)` is transcendental. -/
theorem six_exponentials {x₀ x₁ y₀ y₁ y₂ : ℂ}
    (hx : ∀ a b : ℤ, (a : ℂ) * x₀ + (b : ℂ) * x₁ = 0 → a = 0 ∧ b = 0)
    (hy : ∀ m₀ m₁ m₂ : ℤ, (m₀ : ℂ) * y₀ + (m₁ : ℂ) * y₁ + (m₂ : ℂ) * y₂ = 0 →
      m₀ = 0 ∧ m₁ = 0 ∧ m₂ = 0) :
    ¬ (∀ i : Fin 2, ∀ j : Fin 3, IsAlgebraic ℚ (Complex.exp (![x₀, x₁] i * ![y₀, y₁, y₂] j))) := by
  intro halg
  let D : Data :=
    { x := ![x₀, x₁]
      y := ![y₀, y₁, y₂]
      hx := fun a b h => hx a b (by simpa using h)
      hy := fun m hm => by
        have h := hy (m 0) (m 1) (m 2) (by simpa [Fin.sum_univ_three] using hm)
        funext j
        fin_cases j <;> simp [h.1, h.2.1, h.2.2] }
  exact AlgData.false ⟨D, fun i j => halg i j⟩

end GaloisForLFunctions.RHTower.SixExponentials
