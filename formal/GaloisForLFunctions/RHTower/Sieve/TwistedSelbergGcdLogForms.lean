import GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLog

/-!
# Gcd-logarithmic twisted Selberg log-monomials

For coprime squarefree `a, b` and `i, j ≥ 1`,

`G_{a,b}(i, j, N) = Σ_{m, n ≤ N} μ(m)μ(n)(ma, nb) log(ma, nb)/(mn) · log^i(N/m) log^j(N/n)`.

* **Decomposition** (`twistedGcdLogMonomial_eq`): by
  `c_{a,b} log(ma, nb) = (F' ⋆ G + F ⋆ G') ⋆ P + (F ⋆ G) ⋆ P^{log}`,
  `G_{a,b} = Σ_x F'(x) W_x[G, P] + Σ_x F(x) W_x[G', P] + Σ_x F(x) W_x[G, P^{log}]`, where `W_x[·, P]`
  are the dilated inner sums against the principal and gcd-logarithmic principal models.
* **Cancellation** (`tendsto_twistedGcdLogMonomial_div`): if `ab > 1`,
  `G_{a,b}(q+1, r+1, N)/log^{q+r+2} N → 0`. The first two sums are `O(log^{q+r+1} N)`; the third
  tends to `κ' (Σ F)(Σ G) log^{q+r+2} N` and `F` has total mass zero.
* **Uniform envelope** (`exists_abs_twistedGcdLogMonomial_le`):
  `|G_{a,b}| ≤ M (1 + log ab) d(ab) d(a) d(b) 2^{ω(a)+ω(b)} log^{q+r+2} N` for all such `a, b`.
-/

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-! ## Convolution support and linearity -/

theorem bivariateDirichletConvolution_add_left (f g h : ℕ → ℕ → ℝ) (m n : ℕ) :
    bivariateDirichletConvolution (fun m n => f m n + g m n) h m n =
      bivariateDirichletConvolution f h m n + bivariateDirichletConvolution g h m n := by
  unfold bivariateDirichletConvolution
  split_ifs
  · simp
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- If `f` is supported in `[0, A] × [0, B]` and `g` in `[0, C] × [0, D]`, then `f ⋆ g` is
supported in `[0, AC] × [0, BD]`. -/
theorem bivariateDirichletConvolution_eq_zero_of_support {f g : ℕ → ℕ → ℝ} {A B C D : ℕ}
    (hf : ∀ x y, f x y ≠ 0 → x ≤ A ∧ y ≤ B) (hg : ∀ r s, g r s ≠ 0 → r ≤ C ∧ s ≤ D) {m n : ℕ}
    (h : A * C < m ∨ B * D < n) : bivariateDirichletConvolution f g m n = 0 := by
  unfold bivariateDirichletConvolution
  split_ifs with h0
  · rfl
  refine Finset.sum_eq_zero fun xy _ => ?_
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := xy
  simp only
  by_cases h1 : f x y = 0
  · rw [h1, zero_mul]
  by_cases h2 : g (m / x) (n / y) = 0
  · rw [h2, mul_zero]
  exfalso
  obtain ⟨hxA, hyB⟩ := hf x y h1
  obtain ⟨hrC, hsD⟩ := hg _ _ h2
  have hmle : m ≤ A * C := by
    rw [← Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hx)]
    exact Nat.mul_le_mul hxA hrC
  have hnle : n ≤ B * D := by
    rw [← Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hy)]
    exact Nat.mul_le_mul hyB hsD
  rcases h with h | h
  · exact absurd hmle (not_le.mpr h)
  · exact absurd hnle (not_le.mpr h)

theorem diagMoebius_support {q x y : ℕ} (hq : q ≠ 0) (h : diagMoebius q x y ≠ 0) :
    x ≤ q ∧ y ≤ q := by
  unfold diagMoebius at h
  split_ifs at h with h'
  · obtain ⟨rfl, hx⟩ := h'
    exact ⟨Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hx, Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hx⟩
  · exact absurd rfl h

theorem moebiusDvdPair_support {a b r s : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : moebiusDvdPair a b r s ≠ 0) : r ≤ a * b ∧ s ≤ a * b := by
  unfold moebiusDvdPair moebiusDvd at h
  split_ifs at h with h1 h2
  · exact ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hb) h1).trans (Nat.le_mul_of_pos_left b
      (Nat.pos_of_ne_zero ha)), (Nat.le_of_dvd (Nat.pos_of_ne_zero ha) h2).trans
      (Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero hb))⟩
  all_goals simp at h

/-- `F'` vanishes outside `[1, (ab)²]²`. -/
theorem twistFiniteLog_eq_zero_of_lt {a b m n : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a * b * (a * b) < m ∨ a * b * (a * b) < n) : twistFiniteLog a b m n = 0 := by
  have hq : a * b ≠ 0 := by positivity
  rw [twistFiniteLog_def]
  simp only
  rw [bivariateDirichletConvolution_eq_zero_of_support
      (fun x y hxy => diagMoebius_support hq (fun h0 => hxy (by
        unfold diagMoebiusLog; rw [h0, zero_mul])))
      (fun r s hrs => moebiusDvdPair_support ha hb hrs) h,
    bivariateDirichletConvolution_eq_zero_of_support
      (fun x y hxy => diagMoebius_support hq hxy)
      (fun r s hrs => moebiusDvdPair_support ha hb (fun h0 => hrs (by
        unfold moebiusDvdPairLog; rw [h0, zero_mul]))) h, add_zero]

/-! ## Masses -/

theorem abs_diagMoebiusLog_le {q : ℕ} (hq : q ≠ 0) (m n : ℕ) :
    |diagMoebiusLog q m n| ≤ Real.log q * |diagMoebius q m n| := by
  unfold diagMoebiusLog
  rw [abs_mul, mul_comm]
  by_cases h : m = n ∧ m ∣ q
  · have hm : 0 < m := Nat.pos_of_dvd_of_pos h.2 (Nat.pos_of_ne_zero hq)
    have hmq : m ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) h.2
    rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hm))]
    exact mul_le_mul_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmq)) (abs_nonneg _)
  · have h0 : diagMoebius q m n = 0 := by unfold diagMoebius; rw [if_neg h]
    rw [h0]
    simp

theorem abs_moebiusDvdPairLog_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (m n : ℕ) :
    |moebiusDvdPairLog a b m n| ≤ Real.log ((a * b : ℕ) : ℝ) * |moebiusDvdPair a b m n| := by
  unfold moebiusDvdPairLog
  rw [abs_mul, mul_comm]
  by_cases h : m ∣ b ∧ n ∣ a
  · have hm : 0 < m := Nat.pos_of_dvd_of_pos h.1 (Nat.pos_of_ne_zero hb)
    have hn : 0 < n := Nat.pos_of_dvd_of_pos h.2 (Nat.pos_of_ne_zero ha)
    have hmn : m * n ≤ a * b := by
      rw [mul_comm a b]
      exact Nat.mul_le_mul (Nat.le_of_dvd (Nat.pos_of_ne_zero hb) h.1)
        (Nat.le_of_dvd (Nat.pos_of_ne_zero ha) h.2)
    rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast Nat.mul_pos hm hn))]
    exact mul_le_mul_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast Nat.mul_pos hm hn) (by exact_mod_cast hmn))
      (abs_nonneg _)
  · have h0 : moebiusDvdPair a b m n = 0 := by
      unfold moebiusDvdPair moebiusDvd
      rcases not_and_or.mp h with h | h
      · rw [if_neg h, zero_mul]
      · rw [if_neg h, mul_zero]
    rw [h0]
    simp

/-- The absolute mass of `F'` is at most `2 log(ab) d(ab) d(b) d(a)`. -/
theorem sum_Icc_abs_twistFiniteLog_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (X Y : ℕ) :
    ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, |twistFiniteLog a b m n| ≤
      2 * Real.log ((a * b : ℕ) : ℝ) *
        (((a * b).divisors.card : ℝ) * ((b.divisors.card : ℝ) * a.divisors.card)) := by
  have hq : a * b ≠ 0 := by positivity
  have hL : 0 ≤ Real.log ((a * b : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq)
  have h1 := sum_Icc_bivariateDirichletConvolution_le
    (f := fun x y => |diagMoebiusLog (a * b) x y|) (g := fun x y => |moebiusDvdPair a b x y|)
    (A := Real.log ((a * b : ℕ) : ℝ) * ((a * b).divisors.card : ℝ))
    (fun _ _ => abs_nonneg _) (fun X Y => ?_) (sum_Icc_abs_moebiusDvdPair_le ha hb)
    (by positivity) X Y
  · have h2 := sum_Icc_bivariateDirichletConvolution_le
      (f := fun x y => |diagMoebius (a * b) x y|) (g := fun x y => |moebiusDvdPairLog a b x y|)
      (B := Real.log ((a * b : ℕ) : ℝ) * ((b.divisors.card : ℝ) * a.divisors.card))
      (fun _ _ => abs_nonneg _) (sum_Icc_abs_diagMoebius_le hq) (fun X Y => ?_)
      (by positivity) X Y
    · calc ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, |twistFiniteLog a b m n|
          ≤ ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
              (bivariateDirichletConvolution (fun x y => |diagMoebiusLog (a * b) x y|)
                  (fun x y => |moebiusDvdPair a b x y|) m n +
                bivariateDirichletConvolution (fun x y => |diagMoebius (a * b) x y|)
                  (fun x y => |moebiusDvdPairLog a b x y|) m n) := by
            refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => ?_
            rw [twistFiniteLog_def]
            exact (abs_add_le _ _).trans (add_le_add
              (abs_bivariateDirichletConvolution_le _ _ m n)
              (abs_bivariateDirichletConvolution_le _ _ m n))
        _ = (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
              bivariateDirichletConvolution (fun x y => |diagMoebiusLog (a * b) x y|)
                (fun x y => |moebiusDvdPair a b x y|) m n) +
            ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y,
              bivariateDirichletConvolution (fun x y => |diagMoebius (a * b) x y|)
                (fun x y => |moebiusDvdPairLog a b x y|) m n := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_add_distrib
        _ ≤ _ := add_le_add h1 h2
        _ = _ := by ring
    · calc ∑ r ∈ Finset.Icc 1 X, ∑ s ∈ Finset.Icc 1 Y, |moebiusDvdPairLog a b r s|
          ≤ ∑ r ∈ Finset.Icc 1 X, ∑ s ∈ Finset.Icc 1 Y,
              Real.log ((a * b : ℕ) : ℝ) * |moebiusDvdPair a b r s| :=
            Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ =>
              abs_moebiusDvdPairLog_le ha hb r s
        _ = Real.log ((a * b : ℕ) : ℝ) *
              ∑ r ∈ Finset.Icc 1 X, ∑ s ∈ Finset.Icc 1 Y, |moebiusDvdPair a b r s| := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_abs_moebiusDvdPair_le ha hb X Y) hL
  · calc ∑ x ∈ Finset.Icc 1 X, ∑ y ∈ Finset.Icc 1 Y, |diagMoebiusLog (a * b) x y|
        ≤ ∑ x ∈ Finset.Icc 1 X, ∑ y ∈ Finset.Icc 1 Y,
            Real.log ((a * b : ℕ) : ℝ) * |diagMoebius (a * b) x y| :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
            abs_diagMoebiusLog_le hq x y
      _ = Real.log ((a * b : ℕ) : ℝ) *
            ∑ x ∈ Finset.Icc 1 X, ∑ y ∈ Finset.Icc 1 Y, |diagMoebius (a * b) x y| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_abs_diagMoebius_le hq X Y) hL

theorem twistSummableLog_zero_left (a b n : ℕ) : twistSummableLog a b 0 n = 0 := by
  simp [twistSummableLog, bivariateDirichletConvolution]

theorem twistSummableLog_zero_right (a b m : ℕ) : twistSummableLog a b m 0 = 0 := by
  simp [twistSummableLog, bivariateDirichletConvolution]

/-- The mass bound `‖E'‖₁ 2^{ω(a)} 2^{ω(b)}` for finite sums of `|E'_{ab} ⋆ R_{b,a}|`. -/
theorem sum_Icc_abs_twistSummableLog_le (a b X Y : ℕ) :
    ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, |twistSummableLog a b m n| ≤
      (∑' mn : ℕ × ℕ, |selbergEulerCorrectionLogCoeff mn.1 mn.2|) *
        ((2 : ℝ) ^ b.primeFactors.card * 2 ^ a.primeFactors.card) := by
  have hsumE := summable_abs_selbergEulerCorrectionLogCoeff
  refine (Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ =>
    abs_bivariateDirichletConvolution_le _ _ m n).trans ?_
  refine sum_Icc_bivariateDirichletConvolution_le (fun _ _ => abs_nonneg _) (fun X Y => ?_)
    (sum_Icc_abs_smoothRecipPair_le a b) (by positivity) X Y
  calc ∑ a' ∈ Finset.Icc 1 X, ∑ b' ∈ Finset.Icc 1 Y, |corrLogCoprime (a * b) a' b'|
      ≤ ∑ x ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y, |selbergEulerCorrectionLogCoeff x.1 x.2| := by
        rw [Finset.sum_product]
        refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
        unfold corrLogCoprime; split_ifs <;> simp
    _ ≤ ∑' mn : ℕ × ℕ, |selbergEulerCorrectionLogCoeff mn.1 mn.2| :=
        hsumE.sum_le_tsum _ fun _ _ => abs_nonneg _

theorem summable_abs_twistSummableLog (a b : ℕ) :
    Summable (fun mn : ℕ × ℕ => |twistSummableLog a b mn.1 mn.2|) :=
  summable_abs_of_sum_Icc_le (twistSummableLog_zero_left a b) (twistSummableLog_zero_right a b)
    fun X => sum_Icc_abs_twistSummableLog_le a b X X

/-! ## The gcd-logarithmic twisted log-monomials -/

/-- The gcd-logarithmic twisted log-monomial `G_{a,b}(i, j, N)`. -/
def twistedGcdLogMonomial (a b i j N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, twistedGcdLogCoeff a b m n *
    (Real.log ((N : ℝ) / (m : ℝ)) ^ i * Real.log ((N : ℝ) / (n : ℝ)) ^ j)

/-- **The decomposition of `G_{a,b}` into three dilated sums.** -/
theorem twistedGcdLogMonomial_eq {a b : ℕ} (hab : Nat.Coprime a b) (ha : Squarefree a)
    (hb : Squarefree b) (i j N : ℕ) :
    twistedGcdLogMonomial a b i j N =
      (∑ x₁ ∈ Finset.Icc 1 N, ∑ x₂ ∈ Finset.Icc 1 N, twistFiniteLog a b x₁ x₂ *
          dilatedInner (twistSummable a b) (selbergPrincipalScaledLogPowerModel i j) x₁ x₂ N) +
        (∑ x₁ ∈ Finset.Icc 1 N, ∑ x₂ ∈ Finset.Icc 1 N, twistFinite a b x₁ x₂ *
          dilatedInner (twistSummableLog a b) (selbergPrincipalScaledLogPowerModel i j) x₁ x₂ N) +
        ∑ x₁ ∈ Finset.Icc 1 N, ∑ x₂ ∈ Finset.Icc 1 N, twistFinite a b x₁ x₂ *
          dilatedInner (twistSummable a b) (selbergGcdLogPrincipalScaledLogPowerModel i j)
            x₁ x₂ N := by
  set w : ℕ → ℕ → ℕ → ℝ := fun N m n =>
    Real.log ((N : ℝ) / (m : ℝ)) ^ i * Real.log ((N : ℝ) / (n : ℝ)) ^ j with hw
  have hP : ∀ d ∈ Finset.Icc 1 N, ∀ e ∈ Finset.Icc 1 N,
      ∑ r ∈ Finset.Icc 1 (N / d), ∑ s ∈ Finset.Icc 1 (N / e),
        selbergPrincipalCoeff r s * w N (d * r) (e * s) =
          selbergPrincipalScaledLogPowerModel i j d e N := fun d hd e he =>
    selbergPrincipalCoeff_weighted_logPower_eq_scaledModel i j d e N
      (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
  have hPlog : ∀ d ∈ Finset.Icc 1 N, ∀ e ∈ Finset.Icc 1 N,
      ∑ r ∈ Finset.Icc 1 (N / d), ∑ s ∈ Finset.Icc 1 (N / e),
        selbergGcdLogPrincipalCoeff r s * w N (d * r) (e * s) =
          selbergGcdLogPrincipalScaledLogPowerModel i j d e N := fun d hd e he =>
    selbergGcdLogPrincipalCoeff_weighted_logPower_eq_scaledModel i j d e N
      (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
  rw [← sum_Icc_convolution_convolution_mul _ _ _ w _ N hP,
    ← sum_Icc_convolution_convolution_mul _ _ _ w _ N hP,
    ← sum_Icc_convolution_convolution_mul _ _ _ w _ N hPlog,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  unfold twistedGcdLogMonomial
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [twistedGcdLogCoeff_eq_convolution hab ha hb (Finset.mem_Icc.mp hm).1
    (Finset.mem_Icc.mp hn).1, twistGcdLogSide_def]
  simp only [hw, bivariateDirichletConvolution_add_left]
  ring

theorem tendsto_inv_log_natCast : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- **Cancellation.** If `ab > 1`, `G_{a,b}(q+1, r+1, N)/log^{q+r+2} N → 0`. -/
theorem tendsto_twistedGcdLogMonomial_div {a b : ℕ} (hab : Nat.Coprime a b) (ha : Squarefree a)
    (hb : Squarefree b) (hab1 : a ≠ 1 ∨ b ≠ 1) (q r : ℕ) :
    Tendsto (fun N : ℕ => twistedGcdLogMonomial a b (q + 1) (r + 1) N / Real.log N ^ (q + r + 2))
      atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_selbergPrincipalScaledLogPowerModel_le q r
  obtain ⟨M', hM0', hM'⟩ := exists_abs_selbergGcdLogPrincipalScaledLogPowerModel_le q r
  have hF : ∀ x₁ x₂, a * b * (a * b) < x₁ ∨ a * b * (a * b) < x₂ → twistFinite a b x₁ x₂ = 0 :=
    fun _ _ hx => twistFinite_eq_zero_of_lt ha.ne_zero hb.ne_zero hx
  have h1 := tendsto_sum_mul_dilatedInner (Φ := selbergPrincipalScaledLogPowerModel (q + 1) (r + 1))
    (a * b * (a * b)) (fun _ _ hx => twistFiniteLog_eq_zero_of_lt ha.ne_zero hb.ne_zero hx)
    (summable_abs_twistSummable a b) (twistSummable_zero_left a b) (twistSummable_zero_right a b)
    (fun hd he => tendsto_selbergPrincipalScaledLogPowerModel_div_log_pow q r hd he) hM0 hM
  have h2 := tendsto_sum_mul_dilatedInner (Φ := selbergPrincipalScaledLogPowerModel (q + 1) (r + 1))
    (a * b * (a * b)) hF
    (summable_abs_twistSummableLog a b) (twistSummableLog_zero_left a b)
    (twistSummableLog_zero_right a b)
    (fun hd he => tendsto_selbergPrincipalScaledLogPowerModel_div_log_pow q r hd he) hM0 hM
  have h3 := tendsto_sum_mul_dilatedInner
    (Φ := selbergGcdLogPrincipalScaledLogPowerModel (q + 1) (r + 1)) (a * b * (a * b)) hF
    (summable_abs_twistSummable a b) (twistSummable_zero_left a b) (twistSummable_zero_right a b)
    (fun hd he => tendsto_selbergGcdLogPrincipalScaledLogPowerModel_div_log_pow q r hd he) hM0' hM'
  rw [sum_twistFinite_eq_zero ha.ne_zero hb.ne_zero hab1 le_rfl, zero_mul] at h3
  have hsum := ((h1.mul tendsto_inv_log_natCast).add (h2.mul tendsto_inv_log_natCast)).add h3
  rw [mul_zero, mul_zero, add_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [twistedGcdLogMonomial_eq hab ha hb, show q + r + 2 = (q + r + 1) + 1 from rfl, pow_succ]
  field_simp
  ring

/-- **Uniform envelope** of the gcd-logarithmic twisted log-monomials. -/
theorem exists_abs_twistedGcdLogMonomial_le (q r : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop, ∀ a b : ℕ, Nat.Coprime a b → Squarefree a →
      Squarefree b →
      |twistedGcdLogMonomial a b (q + 1) (r + 1) N| ≤
        M * ((1 + Real.log ((a * b : ℕ) : ℝ)) *
          (((a * b).divisors.card : ℝ) * ((b.divisors.card : ℝ) * a.divisors.card) *
            ((2 : ℝ) ^ b.primeFactors.card * 2 ^ a.primeFactors.card))) *
          Real.log N ^ (q + r + 2) := by
  obtain ⟨M₁, hM₁, hM₁b⟩ := exists_abs_selbergPrincipalScaledLogPowerModel_le q r
  obtain ⟨M₂, hM₂, hM₂b⟩ := exists_abs_selbergGcdLogPrincipalScaledLogPowerModel_le q r
  set E₁ : ℝ := ∑' mn : ℕ × ℕ, |selbergEulerCorrectionCoeff mn.1 mn.2|
  set E₂ : ℝ := ∑' mn : ℕ × ℕ, |selbergEulerCorrectionLogCoeff mn.1 mn.2|
  have hE₁ : 0 ≤ E₁ := tsum_nonneg fun _ => abs_nonneg _
  have hE₂ : 0 ≤ E₂ := tsum_nonneg fun _ => abs_nonneg _
  refine ⟨2 * E₁ * M₁ + E₂ * M₁ + E₁ * M₂, by positivity, ?_⟩
  filter_upwards [hM₁b, hM₂b, eventually_ge_atTop 3] with N hN₁ hN₂ hN3 a b hab ha hb
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    exact (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)).le.trans h3
  have hP : Real.log N ^ (q + r + 1) ≤ Real.log N ^ (q + r + 2) :=
    pow_le_pow_right₀ hL1 (by omega)
  have hP0 : 0 ≤ Real.log N ^ (q + r + 1) := pow_nonneg (by linarith) _
  have hab0 : a * b ≠ 0 := Nat.mul_ne_zero ha.ne_zero hb.ne_zero
  set ℓ : ℝ := Real.log ((a * b : ℕ) : ℝ)
  have hℓ : 0 ≤ ℓ := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hab0)
  set K₁ : ℝ := ((a * b).divisors.card : ℝ) * ((b.divisors.card : ℝ) * a.divisors.card)
  set K₂ : ℝ := (2 : ℝ) ^ b.primeFactors.card * 2 ^ a.primeFactors.card
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  have t1 := abs_sum_mul_dilatedInner_le (sum_Icc_abs_twistFiniteLog_le ha.ne_zero hb.ne_zero N N)
    (sum_Icc_abs_twistSummable_le a b) hN₁ (by positivity) (by positivity)
  have t2 := abs_sum_mul_dilatedInner_le (sum_Icc_abs_twistFinite_le ha.ne_zero hb.ne_zero N N)
    (sum_Icc_abs_twistSummableLog_le a b) hN₁ (by positivity) (by positivity)
  have t3 := abs_sum_mul_dilatedInner_le (sum_Icc_abs_twistFinite_le ha.ne_zero hb.ne_zero N N)
    (sum_Icc_abs_twistSummable_le a b) hN₂ (by positivity) (by positivity)
  rw [twistedGcdLogMonomial_eq hab ha hb]
  refine (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add t1 t2)) t3).trans ?_)
  have e1 : 2 * ℓ * K₁ * (E₁ * K₂ * (M₁ * Real.log N ^ (q + r + 1))) ≤
      2 * E₁ * M₁ * ((1 + ℓ) * (K₁ * K₂)) * Real.log N ^ (q + r + 2) := by
    have : ℓ * Real.log N ^ (q + r + 1) ≤ (1 + ℓ) * Real.log N ^ (q + r + 2) :=
      mul_le_mul (by linarith) hP hP0 (by linarith)
    have hc : 0 ≤ 2 * E₁ * M₁ * (K₁ * K₂) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hc]
  have e2 : K₁ * (E₂ * K₂ * (M₁ * Real.log N ^ (q + r + 1))) ≤
      E₂ * M₁ * ((1 + ℓ) * (K₁ * K₂)) * Real.log N ^ (q + r + 2) := by
    have : Real.log N ^ (q + r + 1) ≤ (1 + ℓ) * Real.log N ^ (q + r + 2) := by
      nlinarith
    have hc : 0 ≤ E₂ * M₁ * (K₁ * K₂) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hc]
  have e3 : K₁ * (E₁ * K₂ * (M₂ * Real.log N ^ (q + r + 2))) ≤
      E₁ * M₂ * ((1 + ℓ) * (K₁ * K₂)) * Real.log N ^ (q + r + 2) := by
    have : Real.log N ^ (q + r + 2) ≤ (1 + ℓ) * Real.log N ^ (q + r + 2) := by
      nlinarith
    have hc : 0 ≤ E₁ * M₂ * (K₁ * K₂) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hc]
  linarith

end

end RHTower.Sieve
