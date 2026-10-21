import GaloisForLFunctions.BezoutValuationIncidence.IteratedDifferencesAndRisingFactorialPronicWeights

/-!
# The cross-scale law of every order

**The exact tail identity.** Put `t_d(A) = Σ_{M ≥ A} r_d(M) w(M)` for the centred residue `r_d` and the
pronic weight `w`. The step decomposition `⌊M/n⌋ = Σ_j 1[jn ≤ M]` and the rank-two law give, for all
rows,

`B(c, c') + m(c) R(c') + β(c) H(c') = -Σ_{n, d} c'(n) (c(d)/d) Σ_{j ≥ 1} t_d(jn)`.

**The potential chain.** Starting from `X₀ = r_d`, let `Y_i` be the centred periodic primitive of `X_i`
and `X_{i+1}(n) = Y_i(n+1)`. Every `Y_i` is `d`-periodic with zero period sum and
`|Y_i| ≤ (2d)^{i+1} d/2`. Summing by parts against the weights `u_i = Δⁱ w` of the rising-factorial
tower `u_i(A) = (i+1)!/(A(A+1)⋯(A+i+1))` gives, for `1 ≤ A` and every `L`,

`t_d(A) = -Σ_{i < L} Y_i(A) u_i(A) + T_L(A)`,  `|T_L(A)| ≤ (2d)^L (d²/2) u_L(A)`.

**The law of order `L + 1`.** For all rows `c, c'`,

`|B + m R' + β H' - Σ_{n, d} c'(n) (c(d)/d) Σ_{i < L} Σ_{j ≥ 1} Y_{d,i}(jn) u_i(jn)|
  ≤ 2^L (L+1)! Σ_d |c(d)| d^{L+1} Σ_n |c'(n)|/n^{L+2}`.

The second-order law (`L = 1`) and the third-order law (`L = 2`) are the first two cases, with the
`j`-sums of the potentials not yet expanded in powers of `1/n`. Each potential term depends on the
large modulus only through `jn mod d`.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The potential chain -/

/-- The sources `X₀ = r_d`, `X_{i+1}(n) = Y_i(n+1)` of the potential chain. -/
def potentialSource (d : ℕ) : ℕ → ℕ → ℝ
  | 0 => centeredResidue d
  | i + 1 => fun n => centredPrimitive d (potentialSource d i) (n + 1)

/-- The potentials `Y_i`, the centred periodic primitives of the sources. -/
def chainPotential (d i : ℕ) : ℕ → ℝ := centredPrimitive d (potentialSource d i)

theorem potentialSource_succ (d i n : ℕ) :
    potentialSource d (i + 1) n = chainPotential d i (n + 1) := rfl

theorem chainPotential_succ_sub (d i n : ℕ) :
    chainPotential d i (n + 1) - chainPotential d i n = potentialSource d i n :=
  centredPrimitive_succ_sub d _ n

/-- The sources are periodic with zero period sums and `|X_i| ≤ (2d)^i (d/2)`. -/
theorem potentialSource_props {d : ℕ} (hd : 0 < d) (i : ℕ) :
    (∀ n, potentialSource d i (n + d) = potentialSource d i n) ∧
      ∑ n ∈ range d, potentialSource d i n = 0 ∧
      ∀ n, |potentialSource d i n| ≤ (2 * d) ^ i * ((d : ℝ) / 2) := by
  induction i with
  | zero =>
    refine ⟨fun n => by simp only [potentialSource, centeredResidue, Nat.add_mod_right], ?_,
      fun n => ?_⟩
    · have h := sum_Ico_centeredResidue_period d hd 0
      rwa [zero_add, ← range_eq_Ico] at h
    · simp only [potentialSource, pow_zero, one_mul]
      have := abs_centeredResidue_le d n hd
      linarith
  | succ i ih =>
    obtain ⟨hper, h0, hb⟩ := ih
    have hYper := centredPrimitive_periodic hper h0
    refine ⟨fun n => ?_, ?_, fun n => ?_⟩
    · simp only [potentialSource]; rw [show n + d + 1 = n + 1 + d by ring, hYper]
    · have e : ∑ n ∈ range d, potentialSource d (i + 1) n =
          ∑ n ∈ Ico 1 (1 + d), centredPrimitive d (potentialSource d i) n := by
        rw [sum_Ico_eq_sum_range, show 1 + d - 1 = d by omega]
        exact sum_congr rfl fun n _ => by simp only [potentialSource]; rw [add_comm]
      rw [e, sum_Ico_eq_sum_range_of_periodic hYper 1, sum_range_centredPrimitive hd]
    · simp only [potentialSource]
      calc |centredPrimitive d (potentialSource d i) (n + 1)|
          ≤ 2 * d * ((2 * d) ^ i * ((d : ℝ) / 2)) := abs_centredPrimitive_le hd hper h0 hb _
        _ = (2 * d) ^ (i + 1) * ((d : ℝ) / 2) := by ring

theorem chainPotential_periodic {d : ℕ} (hd : 0 < d) (i n : ℕ) :
    chainPotential d i (n + d) = chainPotential d i n :=
  centredPrimitive_periodic (potentialSource_props hd i).1 (potentialSource_props hd i).2.1 n

theorem sum_range_chainPotential {d : ℕ} (hd : 0 < d) (i : ℕ) :
    ∑ n ∈ range d, chainPotential d i n = 0 := sum_range_centredPrimitive hd _

theorem abs_chainPotential_le {d : ℕ} (hd : 0 < d) (i n : ℕ) :
    |chainPotential d i n| ≤ (2 * d) ^ (i + 1) * ((d : ℝ) / 2) := by
  obtain ⟨hper, h0, hb⟩ := potentialSource_props hd i
  calc |chainPotential d i n| ≤ 2 * d * ((2 * d) ^ i * ((d : ℝ) / 2)) :=
        abs_centredPrimitive_le hd hper h0 hb n
    _ = (2 * d) ^ (i + 1) * ((d : ℝ) / 2) := by ring

/-! ## §2. Summation by parts on tails -/

/-- Abel's bound on a tail: antitone nonnegative `g`, interval sums of `x` at most `K`. -/
theorem abs_tsum_mul_antitone_le {x g : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hg0 : ∀ n, 0 ≤ g n)
    (hanti : Antitone g) (hx : ∀ N L, |∑ n ∈ Ico N (N + L), x n| ≤ K)
    (hs : Summable fun n => g n * x n) : |∑' n, g n * x n| ≤ K * g 0 := by
  have hpart : ∀ L, |∑ n ∈ range L, g n * x n| ≤ K * g 0 := fun L => by
    rw [range_eq_Ico]; exact abs_sum_Ico_mul_antitone_le hK hg0 hanti hx 0 L
  exact le_of_tendsto (hs.hasSum.tendsto_sum_nat.abs) (Eventually.of_forall hpart)

/-- One summation by parts on a tail, with bounded `Y` and `u(A + m) → 0`. -/
theorem tsum_sub_mul_eq (Y u : ℕ → ℝ) (A : ℕ) {B : ℝ} (hY : ∀ n, |Y n| ≤ B)
    (hu : Tendsto (fun m => u (A + m)) atTop (𝓝 0))
    (h1 : Summable fun m => (Y (A + m + 1) - Y (A + m)) * u (A + m))
    (h2 : Summable fun m => Y (A + m + 1) * (u (A + m) - u (A + m + 1))) :
    ∑' m, (Y (A + m + 1) - Y (A + m)) * u (A + m) =
      -(Y A * u A) + ∑' m, Y (A + m + 1) * (u (A + m) - u (A + m + 1)) := by
  have hfin : ∀ k, ∑ m ∈ range (k + 1), (Y (A + m + 1) - Y (A + m)) * u (A + m) =
      Y (A + k + 1) * u (A + k) - Y A * u A +
        ∑ m ∈ range k, Y (A + m + 1) * (u (A + m) - u (A + m + 1)) := by
    intro k
    have h := sum_Ico_sub_mul_eq Y u A k
    rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range, show A + k + 1 - A = k + 1 by omega,
      show A + k - A = k by omega] at h
    simpa only [add_assoc] using h
  have hL := h1.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hbd : Tendsto (fun k => Y (A + k + 1) * u (A + k)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) ((hu.abs.const_mul B).trans (by simp))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hY _) (abs_nonneg _)
  have hR := (hbd.sub_const (Y A * u A)).add h2.hasSum.tendsto_sum_nat
  have heq : (fun k => ∑ m ∈ range (k + 1), (Y (A + m + 1) - Y (A + m)) * u (A + m)) =
      fun k => Y (A + k + 1) * u (A + k) - Y A * u A +
        ∑ m ∈ range k, Y (A + m + 1) * (u (A + m) - u (A + m + 1)) := funext hfin
  have hL' : Tendsto (fun k => ∑ m ∈ range (k + 1), (Y (A + m + 1) - Y (A + m)) * u (A + m))
      atTop (𝓝 (∑' m, (Y (A + m + 1) - Y (A + m)) * u (A + m))) := hL
  rw [heq] at hL'
  have := tendsto_nhds_unique hL' hR
  rw [this]; ring

/-! ## §3. The residue tail and its expansion -/

theorem summable_pw_add (A : ℕ) : Summable fun m : ℕ => pw (A + m) := by
  have hs : Summable fun M : ℕ => pw M := by
    refine Summable.of_nonneg_of_le (fun M => pw_nonneg M) (fun M => ?_)
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp [pw]
    · have hM : (0 : ℝ) < M := by exact_mod_cast h
      unfold pw
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  exact ((summable_nat_add_iff A).mpr hs).congr fun m => by rw [add_comm]

theorem summable_centeredResidue_mul_pw {d : ℕ} (hd : 0 < d) (A : ℕ) :
    Summable fun m : ℕ => centeredResidue d (A + m) * pw (A + m) := by
  refine Summable.of_norm_bounded ((summable_pw_add A).mul_left (((d : ℝ) - 1) / 2)) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pw_nonneg _)]
  exact mul_le_mul_of_nonneg_right (abs_centeredResidue_le d _ hd) (pw_nonneg _)

/-- The residue tail `t_d(A) = Σ_{M ≥ A} r_d(M) w(M)`. -/
def residueTail (d A : ℕ) : ℝ := ∑' m, centeredResidue d (A + m) * pw (A + m)

/-- Finite windows are tail differences: `Σ_{A ≤ M < H} r_d(M) w(M) = t_d(A) - t_d(H)`. -/
theorem sum_Ico_centeredResidue_mul_pw_eq_tail {d A H : ℕ} (hd : 0 < d) (hAH : A ≤ H) :
    ∑ M ∈ Ico A H, centeredResidue d M * pw M = residueTail d A - residueTail d H := by
  have h := (summable_centeredResidue_mul_pw hd A).sum_add_tsum_nat_add (H - A)
  unfold residueTail
  rw [← h, sum_Ico_eq_sum_range]
  have : ∑' m, centeredResidue d (A + (m + (H - A))) * pw (A + (m + (H - A))) =
      ∑' m, centeredResidue d (H + m) * pw (H + m) :=
    tsum_congr fun m => by rw [show A + (m + (H - A)) = H + m by omega]
  rw [this]; ring

theorem abs_residueTail_le {d A : ℕ} (hd : 0 < d) (hA : 1 ≤ A) :
    |residueTail d A| ≤ (d : ℝ) ^ 2 / 2 * pw A := by
  have hx : ∀ N L, |∑ n ∈ Ico N (N + L), centeredResidue d (A + n)| ≤ d * ((d : ℝ) / 2) := by
    intro N L
    have h := abs_sum_Ico_le_of_periodic hd (g := centeredResidue d)
      (fun n => by simp only [centeredResidue, Nat.add_mod_right])
      (by have := sum_Ico_centeredResidue_period d hd 0; rwa [zero_add, ← range_eq_Ico] at this)
      (B := (d : ℝ) / 2) (fun n => by have := abs_centeredResidue_le d n hd; linarith) (A + N) L
    rw [sum_Ico_eq_sum_range] at h ⊢
    simp only [show N + L - N = L by omega, show A + N + L - (A + N) = L by omega] at h ⊢
    convert h using 3 with i; ring_nf
  have hanti : Antitone fun m => pw (A + m) := antitone_nat_of_succ_le fun m => by
    rw [← pronicWeight_zero, ← pronicWeight_zero, show A + (m + 1) = A + m + 1 by ring]
    exact pronicWeight_succ_le (by omega)
  have h := abs_tsum_mul_antitone_le (by positivity) (fun m => pw_nonneg _) hanti hx
    ((summable_centeredResidue_mul_pw hd A).congr fun m => by ring)
  unfold residueTail
  rw [tsum_congr fun m => mul_comm (centeredResidue d (A + m)) (pw (A + m))]
  calc |∑' m, pw (A + m) * centeredResidue d (A + m)| ≤ d * ((d : ℝ) / 2) * pw (A + 0) := h
    _ = (d : ℝ) ^ 2 / 2 * pw A := by rw [add_zero]; ring

/-- **The tail expansion to any order.** For `1 ≤ A` and every `L`,
`t_d(A) = -Σ_{i < L} Y_i(A) u_i(A) + Σ_{M ≥ A} X_L(M) u_L(M)`. -/
theorem residueTail_eq_expansion {d A : ℕ} (hd : 0 < d) (hA : 1 ≤ A) (L : ℕ) :
    residueTail d A = -∑ i ∈ range L, chainPotential d i A * pronicWeight i A +
      ∑' m, potentialSource d L (A + m) * pronicWeight L (A + m) := by
  induction L with
  | zero =>
    simp only [range_zero, sum_empty, neg_zero, zero_add, residueTail]
    exact tsum_congr fun m => by rw [pronicWeight_zero]; rfl
  | succ L ih =>
    rw [ih, Finset.sum_range_succ]
    obtain ⟨_, _, hb⟩ := potentialSource_props hd L
    have hYb : ∀ n, |chainPotential d L n| ≤ (2 * d) ^ (L + 1) * ((d : ℝ) / 2) :=
      abs_chainPotential_le hd L
    have hu := (summable_pronicWeight_add (k := L) hA).tendsto_atTop_zero
    have hs1 : Summable fun m =>
        (chainPotential d L (A + m + 1) - chainPotential d L (A + m)) * pronicWeight L (A + m) := by
      refine Summable.of_norm_bounded ((summable_pronicWeight_add (k := L) hA).mul_left
        ((2 * d) ^ L * ((d : ℝ) / 2))) fun m => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pronicWeight_pos (by omega)),
        chainPotential_succ_sub]
      exact mul_le_mul_of_nonneg_right (hb _) (pronicWeight_pos (by omega)).le
    have hs2 : Summable fun m => chainPotential d L (A + m + 1) *
        (pronicWeight L (A + m) - pronicWeight L (A + m + 1)) := by
      refine Summable.of_norm_bounded ((summable_pronicWeight_add (k := L + 1) hA).mul_left
        ((2 * d) ^ (L + 1) * ((d : ℝ) / 2))) fun m => ?_
      rw [Real.norm_eq_abs, abs_mul, pronicWeight_sub_succ (by omega),
        abs_of_pos (pronicWeight_pos (by omega))]
      exact mul_le_mul_of_nonneg_right (hYb _) (pronicWeight_pos (by omega)).le
    have hstep := tsum_sub_mul_eq (chainPotential d L) (pronicWeight L) A hYb hu hs1 hs2
    have e1 : ∑' m, potentialSource d L (A + m) * pronicWeight L (A + m) =
        ∑' m, (chainPotential d L (A + m + 1) - chainPotential d L (A + m)) *
          pronicWeight L (A + m) := tsum_congr fun m => by rw [chainPotential_succ_sub]
    have e2 : ∑' m, chainPotential d L (A + m + 1) *
        (pronicWeight L (A + m) - pronicWeight L (A + m + 1)) =
        ∑' m, potentialSource d (L + 1) (A + m) * pronicWeight (L + 1) (A + m) :=
      tsum_congr fun m => by rw [pronicWeight_sub_succ (by omega), potentialSource_succ]
    rw [e1, hstep, e2]
    ring

/-- The remainder of the tail expansion: `|Σ_{M ≥ A} X_L(M) u_L(M)| ≤ (2d)^L (d²/2) u_L(A)`. -/
theorem abs_tail_remainder_le {d A : ℕ} (hd : 0 < d) (hA : 1 ≤ A) (L : ℕ) :
    |∑' m, potentialSource d L (A + m) * pronicWeight L (A + m)| ≤
      (2 * d) ^ L * ((d : ℝ) ^ 2 / 2) * pronicWeight L A := by
  obtain ⟨hper, h0, hb⟩ := potentialSource_props hd L
  have hx : ∀ N K, |∑ n ∈ Ico N (N + K), potentialSource d L (A + n)| ≤
      d * ((2 * d) ^ L * ((d : ℝ) / 2)) := by
    intro N K
    have h := abs_sum_Ico_le_of_periodic hd hper h0 hb (A + N) K
    rw [sum_Ico_eq_sum_range] at h ⊢
    simp only [show N + K - N = K by omega, show A + N + K - (A + N) = K by omega] at h ⊢
    convert h using 3 with i; ring_nf
  have hanti : Antitone fun m => pronicWeight L (A + m) := antitone_nat_of_succ_le fun m => by
    rw [show A + (m + 1) = A + m + 1 by ring]; exact pronicWeight_succ_le (by omega)
  have hs : Summable fun m => pronicWeight L (A + m) * potentialSource d L (A + m) := by
    refine Summable.of_norm_bounded ((summable_pronicWeight_add (k := L) hA).mul_left
      ((2 * d) ^ L * ((d : ℝ) / 2))) fun m => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pronicWeight_pos (by omega)), mul_comm]
    exact mul_le_mul_of_nonneg_right (hb _) (pronicWeight_pos (by omega)).le
  have h := abs_tsum_mul_antitone_le (by positivity) (fun m => (pronicWeight_pos (by omega)).le)
    hanti hx hs
  rw [tsum_congr fun m => mul_comm (potentialSource d L (A + m)) (pronicWeight L (A + m))]
  calc |∑' m, pronicWeight L (A + m) * potentialSource d L (A + m)|
      ≤ d * ((2 * d) ^ L * ((d : ℝ) / 2)) * pronicWeight L (A + 0) := h
    _ = (2 * d) ^ L * ((d : ℝ) ^ 2 / 2) * pronicWeight L A := by rw [add_zero]; ring

/-! ## §4. The exact tail identity -/

/-- `Σ_{j ≥ 1} u_k(jn) ≤ 2 (k+1)!/n^{k+2}`, with summability. -/
theorem summable_pronicWeight_mul {k n : ℕ} (hn : 1 ≤ n) :
    Summable fun i : ℕ => pronicWeight k ((i + 1) * n) := by
  have hs : Summable fun i : ℕ => ((k + 1).factorial : ℝ) / (n : ℝ) ^ (k + 2) *
      (1 / ((i + 1 : ℕ) : ℝ) ^ 2) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left _
  refine Summable.of_nonneg_of_le (fun i => (pronicWeight_pos (by nlinarith)).le)
    (fun i => ?_) hs
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hi : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos i
  refine (pronicWeight_le (by nlinarith)).trans ?_
  push_cast
  rw [mul_pow, div_mul_div_comm, mul_one]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  have : ((i : ℝ) + 1) ^ 2 ≤ ((i : ℝ) + 1) ^ (k + 2) :=
    pow_le_pow_right₀ (by push_cast at hi; linarith) (by omega)
  nlinarith [pow_pos (by linarith : (0 : ℝ) < n) (k + 2)]

theorem tsum_pronicWeight_mul_le {k n : ℕ} (hn : 1 ≤ n) :
    ∑' i : ℕ, pronicWeight k ((i + 1) * n) ≤ 2 * ((k + 1).factorial : ℝ) / (n : ℝ) ^ (k + 2) := by
  have hz : HasSum (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hb := hz.mul_left (((k + 1).factorial : ℝ) / (n : ℝ) ^ (k + 2))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle := Summable.tsum_le_tsum (fun i => ?_) (summable_pronicWeight_mul (k := k) hn) hb.summable
  · rw [hb.tsum_eq] at hle
    have hpi : Real.pi ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    calc ∑' i : ℕ, pronicWeight k ((i + 1) * n)
        ≤ ((k + 1).factorial : ℝ) / (n : ℝ) ^ (k + 2) * (Real.pi ^ 2 / 6) := hle
      _ ≤ ((k + 1).factorial : ℝ) / (n : ℝ) ^ (k + 2) * 2 := by gcongr
      _ = 2 * ((k + 1).factorial : ℝ) / (n : ℝ) ^ (k + 2) := by ring
  · have hi : (1 : ℝ) ≤ (i : ℝ) + 1 := by have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith
    refine (pronicWeight_le (by nlinarith)).trans ?_
    push_cast
    rw [mul_pow, div_mul_div_comm, mul_one]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    have : ((i : ℝ) + 1) ^ 2 ≤ ((i : ℝ) + 1) ^ (k + 2) := pow_le_pow_right₀ hi (by omega)
    nlinarith [pow_pos (by linarith : (0 : ℝ) < n) (k + 2)]

theorem summable_residueTail_mul {d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n) :
    Summable fun i : ℕ => residueTail d ((i + 1) * n) := by
  refine Summable.of_norm_bounded ((summable_pronicWeight_mul (k := 0) hn).mul_left
    ((d : ℝ) ^ 2 / 2)) fun i => ?_
  rw [Real.norm_eq_abs, pronicWeight_zero]
  exact abs_residueTail_le hd (by nlinarith)

/-- The tail sum `τ_d(n) = Σ_{j ≥ 1} t_d(jn)`. -/
def residueTailSum (d n : ℕ) : ℝ := ∑' i : ℕ, residueTail d ((i + 1) * n)

/-- The window sums of one pair converge to the tail sum. -/
theorem tendsto_sum_Icc_window_tail {d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n) :
    Tendsto (fun H : ℕ => ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, centeredResidue d M * pw M) atTop
      (𝓝 (residueTailSum d n)) := by
  have hsplit : ∀ H, ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, centeredResidue d M * pw M =
      ∑ j ∈ Icc 1 H, (if j * n < H then residueTail d (j * n) else 0) -
        (∑ j ∈ Icc 1 H, (if j * n < H then (1 : ℝ) else 0)) * residueTail d H := by
    intro H
    rw [sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [sum_Ico_centeredResidue_mul_pw_eq_tail hd h.le]; ring
    · rw [Ico_eq_empty_of_le (not_lt.mp h), sum_empty]; ring
  have h1 := tendsto_sum_Icc_ite_of_hasSum (f := fun j => residueTail d (j * n)) hn
    (summable_residueTail_mul hd hn).hasSum
  have h2 : Tendsto (fun H : ℕ => (∑ j ∈ Icc 1 H, (if j * n < H then (1 : ℝ) else 0)) *
      residueTail d H) atTop (𝓝 0) := by
    have hpw : Tendsto (fun H : ℕ => (d : ℝ) ^ 2 / 2 * ((H : ℝ) * pw H)) atTop (𝓝 0) := by
      have : Tendsto (fun H : ℕ => (H : ℝ) * pw H) atTop (𝓝 0) := by
        refine squeeze_zero' (Eventually.of_forall fun H => by have := pw_nonneg H; positivity)
          (Eventually.of_forall fun H => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
        rcases Nat.eq_zero_or_pos H with h | h
        · subst h; simp
        · have hH : (0 : ℝ) < H := by exact_mod_cast h
          unfold pw
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      simpa using this.const_mul ((d : ℝ) ^ 2 / 2)
    refine squeeze_zero_norm' (eventually_atTop.mpr ⟨1, fun H hH => ?_⟩) hpw
    have hc : |∑ j ∈ Icc 1 H, (if j * n < H then (1 : ℝ) else 0)| ≤ H := by
      rw [abs_of_nonneg (sum_nonneg fun j _ => by split_ifs <;> norm_num)]
      calc ∑ j ∈ Icc 1 H, (if j * n < H then (1 : ℝ) else 0) ≤ ∑ _j ∈ Icc 1 H, (1 : ℝ) :=
            sum_le_sum fun j _ => by split_ifs <;> norm_num
        _ = H := by simp
    rw [Real.norm_eq_abs, abs_mul]
    calc |∑ j ∈ Icc 1 H, (if j * n < H then (1 : ℝ) else 0)| * |residueTail d H|
        ≤ H * ((d : ℝ) ^ 2 / 2 * pw H) :=
          mul_le_mul hc (abs_residueTail_le hd hH) (abs_nonneg _) (Nat.cast_nonneg _)
      _ = (d : ℝ) ^ 2 / 2 * ((H : ℝ) * pw H) := by ring
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  exact Tendsto.congr (fun H => (hsplit H).symm) h3

/-- **The exact tail identity.** For all rows,
`B + m R' + β H' = -Σ_{n, d} c'(n) (c(d)/d) Σ_{j ≥ 1} t_d(jn)`. -/
theorem rowBilinear_add_mean_add_beta_eq_tail (N : ℕ) (c c' : ℕ → ℝ) :
    rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' =
      -∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * residueTailSum d n := by
  have hstep := tendsto_rowStepSum N c c'
  have hrowC9 : ∀ n H, ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, rowFluct N c M * pw M =
      -∑ d ∈ Icc 1 N, c d / d * ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, centeredResidue d M * pw M := by
    intro n H
    simp only [rowFluct, neg_mul, sum_mul, sum_neg_distrib, mul_sum]
    congr 1
    calc ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, ∑ d ∈ Icc 1 N, c d / d * centeredResidue d M * pw M
        = ∑ j ∈ Icc 1 H, ∑ d ∈ Icc 1 N, ∑ M ∈ Ico (j * n) H, c d / d * centeredResidue d M * pw M :=
          sum_congr rfl fun j _ => sum_comm
      _ = ∑ d ∈ Icc 1 N, ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, c d / d * centeredResidue d M * pw M :=
          sum_comm
      _ = _ := sum_congr rfl fun d _ => sum_congr rfl fun j _ => sum_congr rfl fun M _ => by ring
  have hrow : ∀ H, ∑ n ∈ Icc 1 N, c' n *
      ∑ M ∈ range H, rowFluct N c M * ((M / n : ℕ) : ℝ) / (pronicSeq M : ℝ) =
      -∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) *
        ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, centeredResidue d M * pw M := by
    intro H
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [sum_range_mul_div_div_pronic_eq (mem_Icc.mp hn).1, hrowC9, mul_neg, mul_sum]
    congr 1
    exact sum_congr rfl fun d _ => by ring
  simp_rw [hrow] at hstep
  have hlim : Tendsto (fun H : ℕ => -∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) *
      ∑ j ∈ Icc 1 H, ∑ M ∈ Ico (j * n) H, centeredResidue d M * pw M) atTop
      (𝓝 (-∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * residueTailSum d n)) :=
    (tendsto_finsetSum _ fun n hn => tendsto_finsetSum _ fun d hd =>
      (tendsto_sum_Icc_window_tail (mem_Icc.mp hd).1 (mem_Icc.mp hn).1).const_mul _).neg
  exact tendsto_nhds_unique hstep hlim

/-! ## §5. The law of order `L + 1` -/

/-- The potential terms `Σ_{i < L} Σ_{j ≥ 1} Y_{d,i}(jn) u_i(jn)` of one pair. -/
def potentialTerms (d n L : ℕ) : ℝ :=
  ∑ i ∈ range L, ∑' j : ℕ, chainPotential d i ((j + 1) * n) * pronicWeight i ((j + 1) * n)

theorem summable_chainPotential_mul_pronicWeight {d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n) (i : ℕ) :
    Summable fun j : ℕ => chainPotential d i ((j + 1) * n) * pronicWeight i ((j + 1) * n) := by
  refine Summable.of_norm_bounded ((summable_pronicWeight_mul (k := i) hn).mul_left
    ((2 * d) ^ (i + 1) * ((d : ℝ) / 2))) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pronicWeight_pos (by nlinarith))]
  exact mul_le_mul_of_nonneg_right (abs_chainPotential_le hd i _) (pronicWeight_pos (by nlinarith)).le

/-- The tail sum of one pair is minus its potential terms, up to `2^L (L+1)! d^{L+2}/n^{L+2}`. -/
theorem abs_residueTailSum_add_potentialTerms_le {d n : ℕ} (hd : 0 < d) (hn : 1 ≤ n) (L : ℕ) :
    |residueTailSum d n + potentialTerms d n L| ≤
      2 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 2) / (n : ℝ) ^ (L + 2) := by
  set T : ℕ → ℝ := fun j => ∑' m, potentialSource d L ((j + 1) * n + m) *
    pronicWeight L ((j + 1) * n + m)
  have hexp : ∀ j : ℕ, residueTail d ((j + 1) * n) = -∑ i ∈ range L,
      chainPotential d i ((j + 1) * n) * pronicWeight i ((j + 1) * n) + T j := fun j =>
    residueTail_eq_expansion hd (by nlinarith) L
  have hTb : ∀ j, |T j| ≤ (2 * d) ^ L * ((d : ℝ) ^ 2 / 2) * pronicWeight L ((j + 1) * n) :=
    fun j => abs_tail_remainder_le hd (by nlinarith) L
  have hTs : Summable T := Summable.of_norm_bounded
    ((summable_pronicWeight_mul (k := L) hn).mul_left ((2 * d) ^ L * ((d : ℝ) ^ 2 / 2)))
    fun j => by rw [Real.norm_eq_abs]; exact hTb j
  have hsum : residueTailSum d n + potentialTerms d n L = ∑' j, T j := by
    unfold residueTailSum potentialTerms
    rw [tsum_congr hexp, Summable.tsum_add ((summable_sum fun i _ =>
        summable_chainPotential_mul_pronicWeight hd hn i).neg) hTs, tsum_neg,
      Summable.tsum_finsetSum fun i _ => summable_chainPotential_mul_pronicWeight hd hn i]
    ring
  rw [hsum]
  have hb := tsum_pronicWeight_mul_le (k := L) hn
  calc |∑' j, T j| ≤ ∑' j, |T j| := by
        rw [← Real.norm_eq_abs]
        exact (norm_tsum_le_tsum_norm hTs.norm).trans (le_of_eq (tsum_congr fun j => by simp))
    _ ≤ ∑' j, (2 * d) ^ L * ((d : ℝ) ^ 2 / 2) * pronicWeight L ((j + 1) * n) :=
        Summable.tsum_le_tsum hTb hTs.abs ((summable_pronicWeight_mul (k := L) hn).mul_left _)
    _ = (2 * d) ^ L * ((d : ℝ) ^ 2 / 2) * ∑' j, pronicWeight L ((j + 1) * n) := tsum_mul_left
    _ ≤ (2 * d) ^ L * ((d : ℝ) ^ 2 / 2) * (2 * ((L + 1).factorial : ℝ) / (n : ℝ) ^ (L + 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 2) / (n : ℝ) ^ (L + 2) := by ring

/-- **The cross-scale law of order `L + 1`.** For all rows `c, c'` and every `L`,
`|B + m R' + β H' - Σ_{n, d} c'(n) (c(d)/d) Σ_{i < L} Σ_{j ≥ 1} Y_{d,i}(jn) u_i(jn)|
  ≤ 2^L (L+1)! Σ_d |c(d)| d^{L+1} Σ_n |c'(n)|/n^{L+2}`. -/
theorem abs_rowBilinear_add_mean_add_beta_sub_potentialTerms_le (N L : ℕ) (c c' : ℕ → ℝ) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' -
        ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * potentialTerms d n L| ≤
      2 ^ L * ((L + 1).factorial : ℝ) * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ (L + 1)) *
        ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (L + 2) := by
  rw [rowBilinear_add_mean_add_beta_eq_tail]
  have e : -∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * residueTailSum d n -
      ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * potentialTerms d n L =
      -∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) *
        (residueTailSum d n + potentialTerms d n L) := by
    rw [show ∀ a b : ℝ, -a - b = -(a + b) from fun a b => by ring, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun d _ => by ring
  rw [e, abs_neg]
  have hprod : 2 ^ L * ((L + 1).factorial : ℝ) * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ (L + 1)) *
      ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ (L + 2) =
      ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, |c' n| * (|c d| / d) *
        (2 ^ L * ((L + 1).factorial : ℝ) * (d : ℝ) ^ (L + 2) / (n : ℝ) ^ (L + 2)) := by
    rw [mul_assoc, sum_mul_sum, sum_comm, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun d hd => ?_
    have hdR : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    field_simp
    ring
  rw [hprod]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d hd => ?_)
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [abs_mul, abs_mul, abs_div, abs_of_pos hdR]
  exact mul_le_mul_of_nonneg_left
    (abs_residueTailSum_add_potentialTerms_le hd0 (mem_Icc.mp hn).1 L) (by positivity)

end

end GaloisForLFunctions.BezoutValuationIncidence
