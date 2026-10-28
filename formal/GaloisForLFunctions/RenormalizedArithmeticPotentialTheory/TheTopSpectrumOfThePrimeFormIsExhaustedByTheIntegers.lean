import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePrimeChainHasTheSpectrumOfTheIntegers
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSpectralGapOfThePrimeFormIsTwoLogTwo
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheDifferentOfATorsionOrbit

/-!
# The top spectrum of the prime form is exhausted by the integers

Below `log N − γ`, the spectrum of Weil's atomic prime form `P_N` within any bounded distance `T`
comes only from integers `m` with `log m + d(m) < T`, where `d(m) = Σ_{p∣m} log p/(p − 1)` is the
tame different (`tameDifferent`).

* **Exhaustion** (`eventually_atomicWeilForm_le_of_modes`): for `T, ε > 0`, eventually in `N`, there
  is a finite set `S` of integers with `log m + d(m) < T` and vectors `v_m` (`modeVec`), `m ∈ S`, such
  that `P_N(x) ≤ (log N − γ − T + ε)|x|²` whenever `x ⊥ v_m` for all `m ∈ S`. By Courant–Fischer,
  `P_N` has at most `#{m : log m + d(m) < T}` eigenvalues above `log N − γ − T + ε`.
* **Mechanism.** In the pole gauge `y = √n x`, `P_N ≈ (log N − γ) − D_N`, so the claim is the
  Poincaré inequality `D_N(x) ≥ (T − ε)|x|²` on the complement (`eventually_mul_sum_sq_le_poleDefect`).
  The vectors `v_m` read the fibre means `h` of `y` over the `Q`-smooth parts against the product
  modes `Ψ_m` of the finite prime box. There the spectral inequality `boxSpectral` holds with no
  penalty (`smoothVar_mul_le_of_orthogonal`), and the two scales of `two_scale_le` assemble as for
  the gap `2 log 2`. The box eigenvalues `λ(m)` exceed `log m + d(m)` by at most
  `L_Q 2^{−(X + 1 − K)}` (`log_add_tameDifferent_le_boxEig`).
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticIntersectionTheory

local notation "γ" => Real.eulerMascheroniConstant

/-! ### 1. The smooth chain below a level -/

theorem boxEig_one (J Q : ℕ) : boxEig J Q 1 = 0 := by
  simp [boxEig, ladEig]

theorem boxMode_one (J Q a : ℕ) : boxMode J Q 1 a = 1 := by
  simp [boxMode, ladMode]

/-- **The smooth chain on the complement of the low modes.** If `h` on the `Q`-smooth numbers of
`[1, X]` is orthogonal to every product mode `Ψ_m` with `λ(m) < T`, then its mean vanishes and
`(T − 4L/X^{1/4} − 16LM/log X) Var ≤ (1 + 16L/log X) E`. -/
theorem smoothVar_mul_le_of_orthogonal {Q X : ℕ} (hX : 2 ≤ X) {T : ℝ} (hT : 0 < T) (h : ℕ → ℝ)
    (horth : ∀ m ∈ smoothBox X Q, boxEig X Q m < T →
      ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (h a * boxMode X Q m a) = 0) :
    wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h = 0 ∧
      (T - 4 * logSum Q / Real.sqrt (Real.sqrt X) -
          16 * logSum Q * ladderConstant Q / Real.log X) * smoothVar Q X h ≤
        (1 + 16 * logSum Q / Real.log X) * smoothEnergy Q X h := by
  have h1 := horth 1 (one_mem_smoothBox X Q) (by rw [boxEig_one]; exact hT)
  simp only [boxMode_one, mul_one] at h1
  have hc : wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h = 0 := by
    rw [wMean, h1, zero_div]
  refine ⟨hc, smoothVar_mul_le_of_box hX h ?_⟩
  -- the zero extension lives on `[1, X]`
  have hext : ∀ g : ℕ → ℝ, ∑ a ∈ smoothBox X Q, 1 / (a : ℝ) * (zeroExt Q X h a * g a) =
      ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (h a * g a) := by
    intro g
    rw [← sum_subset (smoothSet_subset_smoothBox Q X) (fun a ha ha' => ?_)]
    · refine sum_congr rfl fun a ha => ?_
      rw [zeroExt, if_pos (mem_smoothSet.mp ha).2.1, hc, sub_zero]
    · have : ¬ a ≤ X := fun hle => ha' (mem_smoothSet.mpr
        ⟨(mem_smoothBox.mp ha).1, hle, (mem_smoothBox.mp ha).2.1⟩)
      rw [zeroExt, if_neg this, zero_mul, mul_zero]
  have hpen : boxPenalty X Q T (zeroExt Q X h) = 0 := by
    refine sum_eq_zero fun m hm => ?_
    split_ifs with hlt
    · rw [show boxInner X Q (zeroExt Q X h) (boxMode X Q m) = 0 by
        rw [boxInner, hext]; exact horth m hm hlt]
      simp
    · rfl
  have hnorm : boxInner X Q (zeroExt Q X h) (zeroExt Q X h) = smoothVar Q X h := by
    rw [boxInner, hext, smoothVar, wVar, hc]
    refine sum_congr rfl fun a ha => ?_
    rw [zeroExt, if_pos (mem_smoothSet.mp ha).2.1, hc]
    ring
  have hsp := boxSpectral X Q T (zeroExt Q X h)
  rw [hpen, sub_zero, hnorm] at hsp
  exact hsp

/-! ### 2. The mode vectors on `[1, N]` -/

/-- The vector `v_m` with `⟨x, v_m⟩ = Σ_{a ≤ X} (1/a) Ψ_m(a) h_a`, `h_a` the mean of `√n x_n` on the
fibre `a · R(Q, N/a)`. -/
def modeVec (Q X N m n : ℕ) : ℝ :=
  ∑ a ∈ smoothSet Q X, ∑ b ∈ roughInterval Q (N / a), if a * b = n then
    1 / (a : ℝ) * boxMode X Q m a / roughHarmonic Q (N / a) * (1 / (b : ℝ)) *
      Real.sqrt ((a * b : ℕ) : ℝ) else 0

theorem sum_mul_modeVec {Q X N : ℕ} (m : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, x n * modeVec Q X N m n =
      ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (fibreMean Q N (poleGauge x) a * boxMode X Q m a) := by
  set C : ℕ → ℕ → ℝ := fun a b => 1 / (a : ℝ) * boxMode X Q m a / roughHarmonic Q (N / a) *
    (1 / (b : ℝ)) * Real.sqrt ((a * b : ℕ) : ℝ)
  have key : ∀ a ∈ smoothSet Q X, ∑ n ∈ Icc 1 N, ∑ b ∈ roughInterval Q (N / a),
      x n * (if a * b = n then C a b else 0) = ∑ b ∈ roughInterval Q (N / a), x (a * b) * C a b := by
    intro a ha
    have ha1 := (mem_smoothSet.mp ha).1
    rw [sum_comm]
    refine sum_congr rfl fun b hb => ?_
    obtain ⟨hb1, hbN, -⟩ := mem_roughInterval.mp hb
    have hab : a * b ∈ Icc 1 N := by
      have h := (Nat.le_div_iff_mul_le (show 0 < a by omega)).mp hbN
      exact mem_Icc.mpr ⟨Nat.mul_pos ha1 hb1, by rw [Nat.mul_comm]; exact h⟩
    simp only [mul_ite, mul_zero]
    rw [sum_ite_eq, if_pos hab]
  calc ∑ n ∈ Icc 1 N, x n * modeVec Q X N m n
      = ∑ n ∈ Icc 1 N, ∑ a ∈ smoothSet Q X, ∑ b ∈ roughInterval Q (N / a),
          x n * (if a * b = n then C a b else 0) := by simp only [modeVec, mul_sum, C]
    _ = ∑ a ∈ smoothSet Q X, ∑ n ∈ Icc 1 N, ∑ b ∈ roughInterval Q (N / a),
          x n * (if a * b = n then C a b else 0) := sum_comm
    _ = ∑ a ∈ smoothSet Q X, ∑ b ∈ roughInterval Q (N / a), x (a * b) * C a b :=
        sum_congr rfl key
    _ = _ := by
        refine sum_congr rfl fun a _ => ?_
        have hF : fibreMean Q N (poleGauge x) a = (∑ b ∈ roughInterval Q (N / a),
            1 / (b : ℝ) * poleGauge x (a * b)) / roughHarmonic Q (N / a) := rfl
        rw [hF, sum_div, sum_mul, mul_sum]
        refine sum_congr rfl fun b _ => ?_
        simp only [poleGauge, C]
        ring

/-! ### 3. Box eigenvalues and the integers -/

/-- A box mode below `T` sits at an integer level: `log m + d(m) ≤ λ(m) + L_Q 2^{−(X+1−⌈T/log 2⌉)}`. -/
theorem log_add_tameDifferent_le_boxEig {Q X m : ℕ} (hm : m ∈ smoothBox X Q) {T : ℝ}
    (hlt : boxEig X Q m < T) :
    Real.log m + tameDifferent m ≤
      boxEig X Q m + logSum Q * (1 / 2 : ℝ) ^ (X + 1 - ⌈T / Real.log 2⌉₊) := by
  obtain ⟨hm1, hms, -⟩ := mem_smoothBox.mp hm
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K := ⌈T / Real.log 2⌉₊
  have hd : tameDifferent m = ∑ p ∈ (range Q).filter Nat.Prime, if m.factorization p ≠ 0 then
      Real.log p / ((p : ℝ) - 1) else 0 := by
    rw [tameDifferent, ← sum_filter]
    congr 1
    ext p
    simp only [mem_filter, mem_range, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpm, -⟩
      exact ⟨⟨hms p (Nat.mem_primeFactors.mpr ⟨hp, hpm, by omega⟩), hp⟩,
        (Nat.Prime.factorization_pos_of_dvd hp (by omega) hpm).ne'⟩
    · rintro ⟨⟨-, hp⟩, hv⟩
      exact ⟨hp, Nat.dvd_of_factorization_pos hv, by omega⟩
  have hnn : ∀ p ∈ (range Q).filter Nat.Prime, 0 ≤ ladEig p X (m.factorization p) := fun p hp =>
    ladEig_nonneg (mem_filter.mp hp).2.one_lt X _
  have hP : ∀ p ∈ (range Q).filter Nat.Prime, (m.factorization p : ℝ) * Real.log p +
      (if m.factorization p ≠ 0 then Real.log p / ((p : ℝ) - 1) else 0) ≤
        ladEig p X (m.factorization p) + Real.log p * (1 / 2 : ℝ) ^ (X + 1 - K) := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    set k := m.factorization p
    have hw : 0 ≤ Real.log p * (1 / 2 : ℝ) ^ (X + 1 - K) := by positivity
    by_cases hk : k = 0
    · rw [if_neg (not_not.mpr hk), hk, ladEig, if_pos rfl]; push_cast; linarith
    rw [if_pos hk]
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    -- the exponent is small: `k log 2 ≤ λ ≤ λ(m) < T`
    have hkT : (k : ℝ) * Real.log 2 < T := by
      have h1 : ladEig p X k ≤ boxEig X Q m := single_le_sum hnn hp
      have h2 : (k : ℝ) * Real.log p ≤ ladEig p X k := by
        rw [ladEig, if_neg hk]
        nlinarith [ladCorr_pos hpp.one_lt X k]
      have h3 : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * Real.log p :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) (by exact_mod_cast hpp.two_le))
          (Nat.cast_nonneg k)
      linarith
    have hkK : k ≤ K := by
      have : (k : ℝ) < T / Real.log 2 := by rw [lt_div_iff₀ hl2]; exact hkT
      exact_mod_cast (this.le.trans (Nat.le_ceil _))
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have htail : (1 / (p : ℝ)) ^ (X - k + 1) / ((p : ℝ) - 1) ≤ (1 / 2 : ℝ) ^ (X + 1 - K) := by
      have h1 : (1 / (p : ℝ)) ^ (X - k + 1) ≤ (1 / 2 : ℝ) ^ (X - k + 1) :=
        pow_le_pow_left₀ (by positivity) (by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith) _
      have h2 : (1 / 2 : ℝ) ^ (X - k + 1) ≤ (1 / 2 : ℝ) ^ (X + 1 - K) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h3 : (1 / (p : ℝ)) ^ (X - k + 1) / ((p : ℝ) - 1) ≤ (1 / (p : ℝ)) ^ (X - k + 1) :=
        div_le_self (by positivity) (by have : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
                                        linarith)
      linarith
    have hge := ladEig_ge hpp.one_lt (J := X) hk1
    rw [mul_add, mul_one_div] at hge
    have := mul_le_mul_of_nonneg_left htail hlp
    nlinarith
  calc Real.log m + tameDifferent m = ∑ p ∈ (range Q).filter Nat.Prime,
        ((m.factorization p : ℝ) * Real.log p +
          (if m.factorization p ≠ 0 then Real.log p / ((p : ℝ) - 1) else 0)) := by
        rw [log_eq_sum_factorization hm1 hms, hd, ← sum_add_distrib]
    _ ≤ ∑ p ∈ (range Q).filter Nat.Prime,
        (ladEig p X (m.factorization p) + Real.log p * (1 / 2 : ℝ) ^ (X + 1 - K)) := sum_le_sum hP
    _ = _ := by rw [sum_add_distrib, ← sum_mul]; rfl

/-! ### 4. The arithmetic of the final step -/

/-- The two-scale inequality with its parameters in range gives `(T − ε) W ≤ D_S + D_L`. -/
theorem le_of_two_scale {T ε g₁ τ κ L M W U DS DL ρ c : ℝ} (hε : 0 < ε) (hεT : ε < T)
    (hg₁ : T - ε / 2 ≤ g₁) (hg₁T : g₁ ≤ T) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hτε : τ * (4 * (T + 2) ^ 2) ≤ ε) (hML : 2 * M / L ≤ τ) (h2L : 2 / L ≤ τ) (hW0 : 0 ≤ W)
    (hU0 : 0 ≤ U) (hDS0 : 0 ≤ DS) (hDL0 : 0 ≤ DL) (hρ : ρ ≤ 1 + τ) (hc : ρ * c ≤ g₁)
    (hκ : κ * (4 * T) ≤ 1) (hU : U ≤ κ * DL)
    (hcore : g₁ * ((1 - 2 * M / L) * W) ≤ g₁ * U + ρ * ((1 + τ) * DS + c * U) + 2 * g₁ / L * DS) :
    (T - ε) * W ≤ DS + DL := by
  have hg₁0 : 0 < g₁ := by linarith
  have hg0 : 0 < T - ε := by linarith
  have hA : g₁ * (1 - τ) * W ≤ 2 * (g₁ * U) + ((1 + τ) ^ 2 + g₁ * τ) * DS := by
    have e1 : g₁ * (1 - τ) * W ≤ g₁ * ((1 - 2 * M / L) * W) := by
      have : (1 - τ) * W ≤ (1 - 2 * M / L) * W := mul_le_mul_of_nonneg_right (by linarith) hW0
      calc g₁ * (1 - τ) * W = g₁ * ((1 - τ) * W) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hg₁0.le
    have e3 : ρ * (1 + τ) * DS ≤ (1 + τ) ^ 2 * DS := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ (by linarith)) hDS0
    have e4 : ρ * c * U ≤ g₁ * U := mul_le_mul_of_nonneg_right hc hU0
    have e5 : 2 * g₁ / L * DS ≤ g₁ * τ * DS := by
      rw [show 2 * g₁ / L = g₁ * (2 / L) by ring]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2L hg₁0.le) hDS0
    calc g₁ * (1 - τ) * W ≤ g₁ * ((1 - 2 * M / L) * W) := e1
      _ ≤ _ := hcore
      _ = g₁ * U + (ρ * (1 + τ) * DS + ρ * c * U) + 2 * g₁ / L * DS := by ring
      _ ≤ g₁ * U + ((1 + τ) ^ 2 * DS + g₁ * U) + g₁ * τ * DS :=
          add_le_add (add_le_add le_rfl (add_le_add e3 e4)) e5
      _ = _ := by ring
  have hκ0 : 2 * (T - ε) * κ ≤ 1 - τ := by
    rcases le_or_gt κ 0 with h | h
    · nlinarith
    · nlinarith
  have hUL : 2 * (g₁ * U) * (T - ε) ≤ g₁ * (1 - τ) * DL := by
    have h1 := mul_le_mul_of_nonneg_left hU (show 0 ≤ 2 * g₁ * (T - ε) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hκ0 (show 0 ≤ g₁ * DL by positivity)
    nlinarith
  have hnum : (T - ε) * ((1 + τ) ^ 2 + g₁ * τ) ≤ g₁ * (1 - τ) := by
    have hb : 2 * (T - ε) + (T - ε) * τ + (T - ε) * g₁ + g₁ ≤ 2 * (T + 2) ^ 2 := by nlinarith
    have hb' := mul_le_mul_of_nonneg_left hb hτ0.le
    have e : (T - ε) * ((1 + τ) ^ 2 + g₁ * τ) =
        (T - ε) + τ * (2 * (T - ε) + (T - ε) * τ + (T - ε) * g₁) := by ring
    rw [e]
    nlinarith
  have hpos : 0 < g₁ * (1 - τ) := mul_pos hg₁0 (by linarith)
  refine le_of_mul_le_mul_left ?_ hpos
  calc g₁ * (1 - τ) * ((T - ε) * W) = (T - ε) * (g₁ * (1 - τ) * W) := by ring
    _ ≤ (T - ε) * (2 * (g₁ * U) + ((1 + τ) ^ 2 + g₁ * τ) * DS) :=
        mul_le_mul_of_nonneg_left hA hg0.le
    _ = 2 * (g₁ * U) * (T - ε) + (T - ε) * ((1 + τ) ^ 2 + g₁ * τ) * DS := by ring
    _ ≤ g₁ * (1 - τ) * DL + g₁ * (1 - τ) * DS :=
        add_le_add hUL (mul_le_mul_of_nonneg_right hnum hDS0)
    _ = g₁ * (1 - τ) * (DS + DL) := by ring

/-- A prime cutoff `Q ≥ 2` with `K/log Q ≤ C`. -/
theorem exists_cutoff_div_log_le' (K : ℝ) {C : ℝ} (hC : 0 < C) :
    ∃ Q : ℕ, 2 ≤ Q ∧ K / Real.log Q ≤ C := by
  refine ⟨⌈Real.exp (K / C)⌉₊ + 2, by omega, ?_⟩
  have hQ : Real.exp (K / C) ≤ ((⌈Real.exp (K / C)⌉₊ + 2 : ℕ) : ℝ) := by
    have := Nat.le_ceil (Real.exp (K / C))
    push_cast
    linarith
  have hlQ0 : 0 < Real.log ((⌈Real.exp (K / C)⌉₊ + 2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < ⌈Real.exp (K / C)⌉₊ + 2 by omega))
  have h3 : K / C ≤ Real.log ((⌈Real.exp (K / C)⌉₊ + 2 : ℕ) : ℝ) := by
    calc K / C = Real.log (Real.exp (K / C)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) hQ
  rw [div_le_iff₀ hlQ0]
  rw [div_le_iff₀ hC] at h3
  linarith

/-- `Σ_n (1/n)(√n x_n)² = |x|²`. -/
theorem sum_one_div_mul_poleGauge_sq (N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, 1 / (n : ℝ) * (poleGauge x n - 0) ^ 2 = ∑ n ∈ Icc 1 N, x n ^ 2 := by
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [sub_zero, poleGauge, mul_pow, Real.sq_sqrt hn0.le]
  field_simp

/-! ### 5. Exhaustion -/

/-- The walk inequality at fixed parameters: cutoff `Q`, horizon `X`, level `T − ε/8` on the box, and
`F(N/X)` large. -/
theorem mul_sum_sq_le_poleDefect_of_params {T ε τ g₁ K : ℝ} {Q X N : ℕ} (hε : 0 < ε) (hεT : ε < T)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2) (hτε : τ * (4 * (T + 2) ^ 2) ≤ ε) (hK : 0 ≤ K)
    (hKt : ∀ Q X : ℕ, ∀ f : ℕ → ℝ, harmonicVar Q X f ≤ K * glauberForm Q X f) (hQ2 : 2 ≤ Q)
    (hκ : K / Real.log Q * (4 * T) ≤ 1) (hX2 : 2 ≤ X) (hXN : X ≤ N)
    (hML : 2 * ladderConstant Q / Real.log X ≤ τ) (h2L : 2 / Real.log X ≤ τ)
    (hg₁ : T - ε / 2 ≤ g₁) (hg₁T : g₁ ≤ T)
    (he : g₁ * (1 + 16 * logSum Q / Real.log X) ≤ T - ε / 8 - 4 * logSum Q /
      Real.sqrt (Real.sqrt X) - 16 * logSum Q * ladderConstant Q / Real.log X)
    (hG : (1 + Real.log X) / τ + 16 * (1 + 1 / τ) * logSum Q / g₁ ≤ roughHarmonic Q (N / X))
    (x : ℕ → ℝ) (hx : ∀ m ∈ (smoothBox X Q).filter (fun m => boxEig X Q m < T - ε / 8),
      ∑ n ∈ Icc 1 N, x n * modeVec Q X N m n = 0) :
    (T - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ poleDefect N x := by
  have hT' : 0 < T - ε / 8 := by linarith
  have hg₁0 : 0 < g₁ := by linarith
  have hlX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hL := logSum_nonneg Q
  have he₂ : 0 ≤ 16 * logSum Q / Real.log X := by positivity
  have horth : ∀ m ∈ smoothBox X Q, boxEig X Q m < T - ε / 8 →
      ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (fibreMean Q N (poleGauge x) a * boxMode X Q m a) = 0 :=
    fun m hm hlt => by
      rw [← sum_mul_modeVec]; exact hx m (mem_filter.mpr ⟨hm, hlt⟩)
  obtain ⟨hc, hsm⟩ := smoothVar_mul_le_of_orthogonal hX2 hT' (fibreMean Q N (poleGauge x)) horth
  have hV0 : 0 ≤ smoothVar Q X (fibreMean Q N (poleGauge x)) :=
    wVar_nonneg fun _ _ => by positivity
  have hA : g₁ * smoothVar Q X (fibreMean Q N (poleGauge x)) ≤
      smoothEnergy Q X (fibreMean Q N (poleGauge x)) := by
    have h1 := mul_le_mul_of_nonneg_right he hV0
    have h2 : (1 + 16 * logSum Q / Real.log X) * (g₁ * smoothVar Q X (fibreMean Q N (poleGauge x))) ≤
        (1 + 16 * logSum Q / Real.log X) * smoothEnergy Q X (fibreMean Q N (poleGauge x)) := by
      calc _ = g₁ * (1 + 16 * logSum Q / Real.log X) *
            smoothVar Q X (fibreMean Q N (poleGauge x)) := by ring
        _ ≤ _ := h1.trans hsm
    exact le_of_mul_le_mul_left h2 (by linarith)
  have hcore := two_scale_le hX2 hXN hg₁0 hτ0 (poleGauge x) hA
  rw [hc, sum_one_div_mul_poleGauge_sq] at hcore
  have hU := sum_fibreVar_le hK hKt hQ2 N (poleGauge x)
  obtain ⟨hρ, hcc⟩ := ratio_bounds (F := roughHarmonic Q N) (G := roughHarmonic Q (N / X)) hτ0
    hg₁0 hL hlX.le
    (by have := roughHarmonic_sub_div_le Q N (show 1 ≤ X by omega); linarith) hG hτ1
  rw [← walkEnergy_small_add_large Q N x]
  exact le_of_two_scale hε hεT hg₁ hg₁T hτ0 hτ1 hτε hML h2L (sum_nonneg fun _ _ => sq_nonneg _)
    (sum_nonneg fun a _ => mul_nonneg (by positivity) (harmonicVar_nonneg _ _ _))
    (walkEnergy_nonneg _ _ _) (walkEnergy_nonneg _ _ _) hρ hcc hκ hU hcore

/-- **The multiplicative walk below a level.** For `T, ε > 0`, eventually in `N`, there are a finite
set `S` of integers with `log m + d(m) < T` and vectors `v_m`, `m ∈ S`, such that every `x`
orthogonal to all `v_m` has `D_N(x) ≥ (T − ε)|x|²`. -/
theorem eventually_mul_sum_sq_le_poleDefect {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ (Q X : ℕ) (S : Finset ℕ),
      (∀ m ∈ S, 1 ≤ m ∧ Real.log m + tameDifferent m < T) ∧
      ∀ x : ℕ → ℝ, (∀ m ∈ S, ∑ n ∈ Icc 1 N, x n * modeVec Q X N m n = 0) →
        (T - ε) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ poleDefect N x := by
  by_cases hεT : T ≤ ε
  · refine ⟨0, fun N _ => ⟨0, 0, ∅, by simp, fun x _ => ?_⟩⟩
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (sum_nonneg fun _ _ => sq_nonneg _)) (poleDefect_nonneg N x)
  replace hεT := not_le.mp hεT
  have hT' : 0 < T - ε / 8 := by linarith
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = min (1 / 2) (ε / (4 * (T + 2) ^ 2)) := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτdef]; exact lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 / 2 := by rw [hτdef]; exact min_le_left _ _
  have hτε : τ * (4 * (T + 2) ^ 2) ≤ ε := by
    have h := min_le_right (1 / 2 : ℝ) (ε / (4 * (T + 2) ^ 2))
    rw [← hτdef, le_div_iff₀ (by positivity)] at h
    exact h
  -- the large primes
  obtain ⟨K, hK, hKt⟩ := exists_harmonicVar_le_glauberForm_rough
  obtain ⟨Q, hQ2, hκ⟩ := exists_cutoff_div_log_le' K (show 0 < 1 / (4 * T) by positivity)
  have hL := logSum_nonneg Q
  have hM := ladderConstant_nonneg Q
  -- the horizon
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq := (Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun X : ℕ => (1 / 2 : ℝ) ^ (X + 1 - ⌈(T - ε / 8) / Real.log 2⌉₊)) atTop
      (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      ((tendsto_sub_atTop_nat _).comp (tendsto_add_atTop_nat 1))
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (((hlog.eventually_ge_atTop
      (1 + 256 * logSum Q * ladderConstant Q / ε + 128 * logSum Q * T / ε)).and
      (hsq.eventually_ge_atTop (1 + 64 * logSum Q / ε))).and
      (hpow.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (8 * (logSum Q + 1)) by positivity))))
  obtain ⟨X, hXX₁, hX2, hML, h2L, -⟩ := exists_horizon hM hτ0 (by linarith) X₁
  obtain ⟨⟨hlogX, hsqX⟩, hpowX⟩ := hX₁ X hXX₁
  simp only [Function.comp] at hlogX hsqX hpowX
  have hlX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hsX : 0 < Real.sqrt (Real.sqrt X) := by positivity
  -- the errors of the horizon
  obtain ⟨e₁, he₁def⟩ : ∃ e : ℝ, e = 4 * logSum Q / Real.sqrt (Real.sqrt X) +
      16 * logSum Q * ladderConstant Q / Real.log X := ⟨_, rfl⟩
  obtain ⟨e₂, he₂def⟩ : ∃ e : ℝ, e = 16 * logSum Q / Real.log X := ⟨_, rfl⟩
  have he₁ : e₁ ≤ ε / 8 := by
    have h1 : 4 * logSum Q / Real.sqrt (Real.sqrt X) ≤ ε / 16 := by
      rw [div_le_iff₀ hsX]
      have : 64 * logSum Q / ε ≤ Real.sqrt (Real.sqrt X) := by linarith
      rw [div_le_iff₀ hε] at this
      nlinarith
    have h2 : 16 * logSum Q * ladderConstant Q / Real.log X ≤ ε / 16 := by
      rw [div_le_iff₀ hlX]
      have : 256 * logSum Q * ladderConstant Q / ε ≤ Real.log X := by
        have : 0 ≤ 128 * logSum Q * T / ε := by positivity
        linarith
      rw [div_le_iff₀ hε] at this
      nlinarith
    rw [he₁def]; linarith
  have he₂ : T * e₂ ≤ ε / 8 := by
    have : 128 * logSum Q * T / ε ≤ Real.log X := by
      have : 0 ≤ 256 * logSum Q * ladderConstant Q / ε := by positivity
      linarith
    rw [div_le_iff₀ hε] at this
    rw [he₂def, mul_div_assoc', div_le_iff₀ hlX]
    nlinarith
  have he₁0 : 0 ≤ e₁ := by rw [he₁def]; positivity
  have he₂0 : 0 ≤ e₂ := by rw [he₂def]; positivity
  obtain ⟨g₁, hg₁def⟩ : ∃ g : ℝ, g = (T - ε / 8 - e₁) / (1 + e₂) := ⟨_, rfl⟩
  have hg₁ : T - ε / 2 ≤ g₁ := by
    rw [hg₁def, le_div_iff₀ (by linarith)]
    nlinarith
  have hg₁T : g₁ ≤ T := by
    rw [hg₁def, div_le_iff₀ (by linarith)]
    nlinarith
  have hg₁0 : 0 < g₁ := by linarith
  -- the rough mass beyond the horizon
  obtain ⟨N₀, hXN₀, hN₀⟩ := eventually_le_roughHarmonic_div (show 1 ≤ Q by omega)
    (show 1 ≤ X by omega) ((1 + Real.log X) / τ + 16 * (1 + 1 / τ) * logSum Q / g₁)
  refine ⟨N₀, fun N hN => ⟨Q, X, (smoothBox X Q).filter (fun m => boxEig X Q m < T - ε / 8),
    fun m hm => ?_, fun x hx => ?_⟩⟩
  · -- the modes sit at integers below `T`
    obtain ⟨hmB, hlt⟩ := mem_filter.mp hm
    refine ⟨(mem_smoothBox.mp hmB).1, ?_⟩
    have h1 := log_add_tameDifferent_le_boxEig hmB hlt
    have h2 : logSum Q * (1 / 2 : ℝ) ^ (X + 1 - ⌈(T - ε / 8) / Real.log 2⌉₊) ≤ ε / 8 := by
      have h3 := mul_le_mul_of_nonneg_left hpowX.le hL
      have h4 : logSum Q * (ε / (8 * (logSum Q + 1))) ≤ ε / 8 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    linarith
  · have hκ' : K / Real.log Q * (4 * T) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hκ (show 0 ≤ 4 * T by positivity)
      rwa [one_div_mul_cancel (by positivity)] at this
    have he : g₁ * (1 + 16 * logSum Q / Real.log X) ≤ T - ε / 8 - 4 * logSum Q /
        Real.sqrt (Real.sqrt X) - 16 * logSum Q * ladderConstant Q / Real.log X := by
      rw [hg₁def, ← he₂def, div_mul_cancel₀ _ (by linarith), he₁def]
      ring_nf
      exact le_rfl
    exact mul_sum_sq_le_poleDefect_of_params hε hεT hτ0 hτ1 hτε hK.le hKt hQ2 hκ' hX2
      (hXN₀.trans hN) hML h2L hg₁ hg₁T he (hN₀ N hN) x hx

/-- **The top spectrum of the prime form is exhausted by the integers.** For `T, ε > 0`, eventually
in `N`, there are a finite set `S` of integers with `log m + d(m) < T` and vectors `v_m`, `m ∈ S`,
such that `P_N(x) ≤ (log N − γ − T + ε)|x|²` for every `x` orthogonal to all `v_m`. -/
theorem eventually_atomicWeilForm_le_of_modes {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ (Q X : ℕ) (S : Finset ℕ),
      (∀ m ∈ S, 1 ≤ m ∧ Real.log m + tameDifferent m < T) ∧
      ∀ x : ℕ → ℝ, (∀ m ∈ S, ∑ n ∈ Icc 1 N, x n * modeVec Q X N m n = 0) →
        atomicWeilForm N x ≤ (Real.log N - γ - T + ε) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  set ε₁ := min (1 / 2 : ℝ) (ε / (2 * (1 + T)))
  have hε₁ : 0 < ε₁ := lt_min (by norm_num) (by positivity)
  have hε₁2 : ε₁ ≤ 1 / 2 := min_le_left _ _
  have hε₁T : ε₁ * (1 + T) ≤ ε / 2 := by
    have h := min_le_right (1 / 2 : ℝ) (ε / (2 * (1 + T)))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨N₁, hN₁⟩ := eventually_atomicWeilForm_add_poleDefect_le hε₁
  obtain ⟨N₂, hN₂⟩ := eventually_mul_sum_sq_le_poleDefect hT (show 0 < ε / 2 by linarith)
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  obtain ⟨Q, X, S, hS, hD⟩ := hN₂ N (le_of_max_le_right hN)
  refine ⟨Q, X, S, hS, fun x hx => ?_⟩
  have h1 := hN₁ N (le_of_max_le_left hN) x
  have h2 := hD x hx
  have hS0 : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - ε₁ by linarith)
  have h4 := mul_le_mul_of_nonneg_right hε₁T hS0
  have h5 : 0 ≤ ε₁ * (ε / 2) * ∑ n ∈ Icc 1 N, x n ^ 2 := by positivity
  nlinarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
