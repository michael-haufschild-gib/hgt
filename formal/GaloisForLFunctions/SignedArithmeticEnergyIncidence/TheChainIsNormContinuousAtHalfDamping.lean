import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheChainIsCompactAtHalfDamping
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheReceiverIsContinuousAtHalfDamping

/-!
# The chain is norm-continuous at half damping

The Hilbert–Schmidt chains `C_η`, `η > ½`, converge to `C_{½}` in operator norm on `ℓ²`: for every
`ε > 0`, eventually as `η ↓ ½`, `Σ_{n<T} ((C_η − C_{½}) b)(n)² ≤ ε Σ_k b_k²` for every finitely
supported `b` and every horizon `T` (`centeredOperator_norm_tendsto_half`).  The receiver
continuity `C_η r → C_{½} r` is the case `b = r`; here the convergence is uniform over the unit ball.

**Proof.**
* **Columns are dilated receivers.**  With `K = k + 1`, `N = n + 1`, the `k`-th column is
  `K^{−η} X_K − (K/(K+1)) (K+1)^{−η} X_{K+1}`, `X_L(n) = (L/N) P_η(N/L)` (`centeredRow_eq_dilated`).
  A profile `a(⌊y⌋) − c y` read at `N/L` has energy at most `L (5c² + 2 Σ_m (Q(m+1)/(m+1))²)`
  (`sum_sq_dilated_profile_le`): each value of `⌊N/L⌋` is taken at most `L` times.  So the column
  differences are controlled by the receiver differences and `ρ_η − ρ_{½}`, and every column
  converges in `ℓ²` (`column_l2_tendsto_half`, from `orbit_l2_tendsto_half`).
* **Tails are uniformly small** (`exists_centeredOperator_tail_l2_le_uniform`): the energy of
  `C_η` beyond `K` is `≪ K^{−1/10}`, uniformly in `½ ≤ η < 1`.  Finitely many columns and a
  uniform tail give convergence in norm.
-/

open MeasureTheory Set Filter Topology
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### Dilated profiles -/

/-- `#{n < T : (n+1)/L = m} ≤ L`. -/
theorem card_filter_div_eq_le {L : ℕ} (hL : 1 ≤ L) (T m : ℕ) :
    ((Finset.range T).filter fun n => (n + 1) / L = m).card ≤ L := by
  have hmaps : Set.InjOn (fun n => n + 1 - m * L)
      ((Finset.range T).filter fun n => (n + 1) / L = m) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx hy
    have hx1 : m * L ≤ x + 1 := hx.2 ▸ Nat.div_mul_le_self (x + 1) L
    have hy1 : m * L ≤ y + 1 := hy.2 ▸ Nat.div_mul_le_self (y + 1) L
    simp only at hxy
    omega
  calc ((Finset.range T).filter fun n => (n + 1) / L = m).card
      ≤ (Finset.range L).card := Finset.card_le_card_of_injOn _ (fun n hn => by
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hn
        have h2 : n + 1 < (n + 1) / L * L + L := Nat.lt_div_mul_add (by omega)
        rw [hn.2] at h2
        simp only [Finset.coe_range, Set.mem_Iio]
        omega) hmaps
    _ = L := Finset.card_range L

/-- **A profile read at dilated integers**: for `Q(y) = a(⌊y⌋) − c y` with `a(0) = 0`,
`Σ_{n<T} ((L/N) Q(N/L))² ≤ L (5c² + 2 Σ_{m<T} (Q(m+1)/(m+1))²)`, `N = n + 1`. -/
theorem sum_sq_dilated_profile_le (a : ℕ → ℝ) (ha : a 0 = 0) (c : ℝ) {L : ℕ} (hL : 1 ≤ L)
    (T : ℕ) (q : ℕ → ℝ) (hq : ∀ m : ℕ, (a (m + 1) - c * ((m : ℝ) + 1)) / ((m : ℝ) + 1) = q m) :
    ∑ n ∈ Finset.range T, ((L : ℝ) / ((n : ℝ) + 1) *
        (a ((n + 1) / L) - c * (((n : ℝ) + 1) / L))) ^ 2 ≤
      L * (5 * c ^ 2 + 2 * ∑ m ∈ Finset.range T, q m ^ 2) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  -- the majorant `G(m)` of the terms with `(n+1)/L = m`
  set G : ℕ → ℝ := fun m => if m = 0 then c ^ 2 else
    2 * ((a m - c * m) / m) ^ 2 + 2 * c ^ 2 / (m : ℝ) ^ 2 with hG
  have hG0 : ∀ m, 0 ≤ G m := fun m => by simp only [hG]; split_ifs <;> positivity
  have hpt : ∀ n : ℕ, ((L : ℝ) / ((n : ℝ) + 1) * (a ((n + 1) / L) - c * (((n : ℝ) + 1) / L))) ^ 2 ≤
      G ((n + 1) / L) := by
    intro n
    set m := (n + 1) / L with hm
    have hN0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmL : (m : ℝ) * L ≤ (n : ℝ) + 1 := by
      have := Nat.div_mul_le_self (n + 1) L
      exact_mod_cast this
    have hmL' : (n : ℝ) + 1 < ((m : ℝ) + 1) * L := by
      have := Nat.lt_div_mul_add (a := n + 1) (by omega : 0 < L)
      have h' : n + 1 < (m + 1) * L := by rw [hm]; nlinarith
      exact_mod_cast h'
    by_cases hm0 : m = 0
    · have hGv : G 0 = c ^ 2 := by simp [hG]
      have hL0' := hL0.ne'
      have hN0' := hN0.ne'
      have e : (L : ℝ) / ((n : ℝ) + 1) * -(c * (((n : ℝ) + 1) / L)) = -c := by
        field_simp
      rw [hm0, ha, zero_sub, e, neg_sq, hGv]
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
      simp only [hG, hm0, if_false]
      -- `(L/N) Q(N/L) = (L/N)(a m − c m) − c (L/N)(N/L − m)`
      have hy : (m : ℝ) ≤ ((n : ℝ) + 1) / L := by rw [le_div_iff₀ hL0]; linarith
      have hy' : ((n : ℝ) + 1) / L - m < 1 := by
        rw [sub_lt_iff_lt_add, div_lt_iff₀ hL0]; linarith
      have hLN : (L : ℝ) / ((n : ℝ) + 1) ≤ 1 / m := by
        rw [div_le_div_iff₀ hN0 (by linarith)]; linarith
      have hLN0 : 0 ≤ (L : ℝ) / ((n : ℝ) + 1) := by positivity
      set u := (L : ℝ) / ((n : ℝ) + 1)
      set y := ((n : ℝ) + 1) / L
      have hsplit : u * (a m - c * y) = u * (a m - c * m) - c * (u * (y - m)) := by ring
      have h1 : |u * (a m - c * m)| ≤ |a m - c * m| / m := by
        rw [abs_mul, abs_of_nonneg hLN0, div_eq_mul_one_div, mul_comm]
        exact mul_le_mul_of_nonneg_left hLN (abs_nonneg _)
      have h2 : |c * (u * (y - m))| ≤ |c| / m := by
        rw [abs_mul, abs_mul, abs_of_nonneg hLN0, abs_of_nonneg (show (0 : ℝ) ≤ y - m by linarith)]
        calc |c| * (u * (y - m)) ≤ |c| * (1 / m * 1) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hLN hy'.le (by linarith) (by positivity))
                (abs_nonneg _)
          _ = |c| / m := by ring
      rw [hsplit]
      have habs : |u * (a m - c * m) - c * (u * (y - m))| ≤ |a m - c * m| / m + |c| / m :=
        (abs_sub _ _).trans (add_le_add h1 h2)
      calc (u * (a m - c * m) - c * (u * (y - m))) ^ 2
          = |u * (a m - c * m) - c * (u * (y - m))| ^ 2 := (sq_abs _).symm
        _ ≤ (|a m - c * m| / m + |c| / m) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ ≤ 2 * (|a m - c * m| / m) ^ 2 + 2 * (|c| / m) ^ 2 := by
            nlinarith [sq_nonneg (|a m - c * m| / m - |c| / m)]
        _ = 2 * ((a m - c * m) / m) ^ 2 + 2 * c ^ 2 / (m : ℝ) ^ 2 := by
            rw [div_pow, div_pow, div_pow, sq_abs, sq_abs]; ring
  -- group the horizon by the value of `(n+1)/L`
  have hgroup : ∑ n ∈ Finset.range T, G ((n + 1) / L) ≤ L * ∑ m ∈ Finset.range (T + 1), G m := by
    rw [Finset.sum_comp]
    have himg : (Finset.range T).image (fun n => (n + 1) / L) ⊆ Finset.range (T + 1) := by
      intro m hm
      simp only [Finset.mem_image, Finset.mem_range] at hm ⊢
      obtain ⟨n, hn, rfl⟩ := hm
      exact Nat.lt_succ_of_le ((Nat.div_le_self _ _).trans (by omega))
    calc ∑ m ∈ (Finset.range T).image (fun n => (n + 1) / L),
          ((Finset.range T).filter fun n => (n + 1) / L = m).card • G m
        ≤ ∑ m ∈ (Finset.range T).image (fun n => (n + 1) / L), (L : ℝ) * G m := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_div_eq_le hL T m) (hG0 m)
      _ ≤ ∑ m ∈ Finset.range (T + 1), (L : ℝ) * G m :=
          Finset.sum_le_sum_of_subset_of_nonneg himg fun m _ _ => mul_nonneg hL0.le (hG0 m)
      _ = L * ∑ m ∈ Finset.range (T + 1), G m := by rw [Finset.mul_sum]
  -- the majorant sum
  have hGsum : ∑ m ∈ Finset.range (T + 1), G m ≤ 5 * c ^ 2 + 2 * ∑ m ∈ Finset.range T, q m ^ 2 := by
    rw [Finset.sum_range_succ']
    have hG0v : G 0 = c ^ 2 := by simp [hG]
    have hGs : ∀ m : ℕ, G (m + 1) = 2 * q m ^ 2 + 2 * c ^ 2 * (1 / ((m + 1 : ℕ) : ℝ) ^ 2) := by
      intro m
      rw [← hq m]
      simp only [hG, Nat.add_one_ne_zero, ↓reduceIte]
      push_cast
      ring
    rw [hG0v, Finset.sum_congr rfl fun m _ => hGs m, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    have hinv := sum_range_inv_succ_sq_le_two T
    nlinarith [sq_nonneg c]
  calc _ ≤ ∑ n ∈ Finset.range T, G ((n + 1) / L) := Finset.sum_le_sum fun n _ => hpt n
    _ ≤ L * ∑ m ∈ Finset.range (T + 1), G m := hgroup
    _ ≤ _ := mul_le_mul_of_nonneg_left hGsum hL0.le

/-! ### Columns -/

/-- The dilated source `X_L(n) = (L/N) P_η(N/L)`, `N = n + 1`. -/
def dilatedSource (η : ℝ) (L n : ℕ) : ℝ :=
  (L : ℝ) / ((n : ℝ) + 1) * sourceProfile η (((n : ℝ) + 1) / L)

theorem sourceProfile_div_eq (η : ℝ) {L : ℕ} (n : ℕ) :
    sourceProfile η (((n : ℝ) + 1) / L) =
      arithmeticDampingPrefix η ((n + 1) / L) -
        (RHTower.pmPowerDampedDivisorDensity η).re * (((n : ℝ) + 1) / L) := by
  unfold sourceProfile
  rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_div_eq_div (K := ℝ)]

/-- **Columns are dilated receivers**:
`C_η(n, k) = K^{−η} X_K(n) − (K/(K+1)) (K+1)^{−η} X_{K+1}(n)`. -/
theorem centeredRow_eq_dilated (η : ℝ) (n k : ℕ) :
    arithmeticDampingCenteredRow η n k =
      ((k + 1 : ℕ) : ℝ) ^ (-η) * dilatedSource η (k + 1) n -
        (((k + 1 : ℕ) : ℝ) / ((k + 1 + 1 : ℕ) : ℝ)) * ((k + 1 + 1 : ℕ) : ℝ) ^ (-η) *
          dilatedSource η (k + 1 + 1) n := by
  rw [centeredRow_eq_columnProfile]
  unfold columnProfile dilatedSource
  have hK1 : ((k + 1 : ℕ) : ℝ) + 1 = ((k + 1 + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hK1]
  have hN : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hN]
  have h1 : (0 : ℝ) < ((k + 1 + 1 : ℕ) : ℝ) := by positivity
  field_simp

/-- The dilated source difference is a profile `a(⌊y⌋) − c y` with `a(0) = 0`. -/
theorem sum_sq_dilatedSource_sub_le (η η' : ℝ) {L : ℕ} (hL : 1 ≤ L) (T : ℕ) :
    ∑ n ∈ Finset.range T, (dilatedSource η L n - dilatedSource η' L n) ^ 2 ≤
      L * (5 * ((RHTower.pmPowerDampedDivisorDensity η).re -
          (RHTower.pmPowerDampedDivisorDensity η').re) ^ 2 +
        2 * ∑ m ∈ Finset.range T, (orbitCoord η m - orbitCoord η' m) ^ 2) := by
  have ha : arithmeticDampingPrefix η 0 - arithmeticDampingPrefix η' 0 = 0 := by
    simp [arithmeticDampingPrefix]
  have h := sum_sq_dilated_profile_le (fun m : ℕ => arithmeticDampingPrefix η m -
    arithmeticDampingPrefix η' m) ha ((RHTower.pmPowerDampedDivisorDensity η).re -
      (RHTower.pmPowerDampedDivisorDensity η').re) hL T (fun m => orbitCoord η m - orbitCoord η' m)
    (fun m => by
      unfold orbitCoord sourceProfile
      rw [show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
      ring)
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_)) h
  unfold dilatedSource
  rw [sourceProfile_div_eq, sourceProfile_div_eq]
  ring

theorem sum_sq_dilatedSource_le (η : ℝ) {L : ℕ} (hL : 1 ≤ L) (T : ℕ) :
    ∑ n ∈ Finset.range T, dilatedSource η L n ^ 2 ≤
      L * (5 * (RHTower.pmPowerDampedDivisorDensity η).re ^ 2 +
        2 * ∑ m ∈ Finset.range T, orbitCoord η m ^ 2) := by
  have ha : arithmeticDampingPrefix η 0 = 0 := by simp [arithmeticDampingPrefix]
  have h := sum_sq_dilated_profile_le (fun m : ℕ => arithmeticDampingPrefix η m)
    ha (RHTower.pmPowerDampedDivisorDensity η).re hL T (fun m => orbitCoord η m)
    (fun m => by
      unfold orbitCoord sourceProfile
      rw [show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast])
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_)) h
  unfold dilatedSource
  rw [sourceProfile_div_eq]

/-- `(x₁ + x₂ − x₃ − x₄)² ≤ 4(x₁² + x₂² + x₃² + x₄²)`. -/
theorem sq_add_add_sub_sub_le (x₁ x₂ x₃ x₄ : ℝ) :
    (x₁ + x₂ - x₃ - x₄) ^ 2 ≤ 4 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2) := by
  nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₃), sq_nonneg (x₁ + x₄), sq_nonneg (x₂ + x₃),
    sq_nonneg (x₂ + x₄), sq_nonneg (x₃ - x₄)]

/-- `(a₁x₁ + y₁ − a₂x₂ − r y₂)² ≤ 4(x₁² + y₁² + x₂² + y₂²)` for `|a₁|, |a₂|, |r| ≤ 1`. -/
theorem sq_comb_le {a₁ a₂ r : ℝ} (h₁ : |a₁| ≤ 1) (h₂ : |a₂| ≤ 1) (hr : |r| ≤ 1)
    (x₁ y₁ x₂ y₂ : ℝ) :
    (a₁ * x₁ + y₁ - a₂ * x₂ - r * y₂) ^ 2 ≤ 4 * (x₁ ^ 2 + y₁ ^ 2 + x₂ ^ 2 + y₂ ^ 2) := by
  have hc : ∀ a : ℝ, |a| ≤ 1 → ∀ x : ℝ, (a * x) ^ 2 ≤ x ^ 2 := fun a ha x => by
    rw [mul_pow, ← sq_abs a]
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (abs_nonneg _) ha)
  refine (sq_add_add_sub_sub_le _ _ _ _).trans ?_
  linarith [hc _ h₁ x₁, hc _ h₂ x₂, hc _ hr y₂]

/-- **The column difference against the receiver difference**: with `K = k + 1`, `K' = k + 2`,
`‖C_η e_k − C_{½} e_k‖² ≤ 4((K + K') E + ((K^{−η} − K^{−½})² K + (K'^{−η} − K'^{−½})² K') B)`,
`E = 5(ρ_η − ρ_{½})² + 2‖u_η − u_{½}‖²`, `B = 5ρ_{½}² + 2‖u_{½}‖²` at the horizon. -/
theorem sum_sq_column_sub_le {η : ℝ} (hη : 0 ≤ η) (k T : ℕ) :
    ∑ n ∈ Finset.range T,
        (arithmeticDampingCenteredRow η n k - arithmeticDampingCenteredRow (1 / 2) n k) ^ 2 ≤
      4 * ((((k + 1 : ℕ) : ℝ) + ((k + 1 + 1 : ℕ) : ℝ)) *
          (5 * ((RHTower.pmPowerDampedDivisorDensity η).re -
              (RHTower.pmPowerDampedDivisorDensity (1 / 2)).re) ^ 2 +
            2 * ∑ m ∈ Finset.range T, (orbitCoord η m - orbitCoord (1 / 2) m) ^ 2) +
        ((((k + 1 : ℕ) : ℝ) ^ (-η) - ((k + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 * ((k + 1 : ℕ) : ℝ) +
          (((k + 1 + 1 : ℕ) : ℝ) ^ (-η) - ((k + 1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 *
            ((k + 1 + 1 : ℕ) : ℝ)) *
          (5 * (RHTower.pmPowerDampedDivisorDensity (1 / 2)).re ^ 2 +
            2 * ∑ m ∈ Finset.range T, orbitCoord (1 / 2) m ^ 2)) := by
  set K : ℝ := ((k + 1 : ℕ) : ℝ)
  set K' : ℝ := ((k + 1 + 1 : ℕ) : ℝ)
  have hK1 : (1 : ℝ) ≤ K := by show (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ); exact_mod_cast Nat.succ_pos k
  have hKK' : K ≤ K' := by
    show ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ); exact_mod_cast Nat.le_succ (k + 1)
  have hK0 : 0 < K := by linarith
  have hK'0 : 0 < K' := by linarith
  have hα : |K ^ (-η)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; exact Real.rpow_le_one_of_one_le_of_nonpos hK1 (by linarith)
  have hr : |K / K'| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), div_le_one hK'0]; exact hKK'
  have hβ : |K / K' * K' ^ (-η)| ≤ 1 := by
    rw [abs_mul]
    have : |K' ^ (-η)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (hK1.trans hKK') (by linarith)
    calc |K / K'| * |K' ^ (-η)| ≤ 1 * 1 := mul_le_mul hr this (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hpt : ∀ n ∈ Finset.range T,
      (arithmeticDampingCenteredRow η n k - arithmeticDampingCenteredRow (1 / 2) n k) ^ 2 ≤
        4 * ((dilatedSource η (k + 1) n - dilatedSource (1 / 2) (k + 1) n) ^ 2 +
          (K ^ (-η) - K ^ (-(1 / 2 : ℝ))) ^ 2 * dilatedSource (1 / 2) (k + 1) n ^ 2 +
          (dilatedSource η (k + 1 + 1) n - dilatedSource (1 / 2) (k + 1 + 1) n) ^ 2 +
          (K' ^ (-η) - K' ^ (-(1 / 2 : ℝ))) ^ 2 * dilatedSource (1 / 2) (k + 1 + 1) n ^ 2) := by
    intro n _
    rw [centeredRow_eq_dilated, centeredRow_eq_dilated]
    have h := sq_comb_le hα hβ hr (dilatedSource η (k + 1) n - dilatedSource (1 / 2) (k + 1) n)
      ((K ^ (-η) - K ^ (-(1 / 2 : ℝ))) * dilatedSource (1 / 2) (k + 1) n)
      (dilatedSource η (k + 1 + 1) n - dilatedSource (1 / 2) (k + 1 + 1) n)
      ((K' ^ (-η) - K' ^ (-(1 / 2 : ℝ))) * dilatedSource (1 / 2) (k + 1 + 1) n)
    rw [mul_pow, mul_pow] at h
    convert h using 2
    ring
  have hE1 := sum_sq_dilatedSource_sub_le η (1 / 2) (L := k + 1) (by omega) T
  have hE3 := sum_sq_dilatedSource_sub_le η (1 / 2) (L := k + 1 + 1) (by omega) T
  have hE2 := sum_sq_dilatedSource_le (1 / 2) (L := k + 1) (by omega) T
  have hE4 := sum_sq_dilatedSource_le (1 / 2) (L := k + 1 + 1) (by omega) T
  have hd1 : 0 ≤ (K ^ (-η) - K ^ (-(1 / 2 : ℝ))) ^ 2 := sq_nonneg _
  have hd2 : 0 ≤ (K' ^ (-η) - K' ^ (-(1 / 2 : ℝ))) ^ 2 := sq_nonneg _
  have j2 := mul_le_mul_of_nonneg_left hE2 hd1
  have j4 := mul_le_mul_of_nonneg_left hE4 hd2
  calc ∑ n ∈ Finset.range T,
        (arithmeticDampingCenteredRow η n k - arithmeticDampingCenteredRow (1 / 2) n k) ^ 2
      ≤ ∑ n ∈ Finset.range T,
          4 * ((dilatedSource η (k + 1) n - dilatedSource (1 / 2) (k + 1) n) ^ 2 +
          (K ^ (-η) - K ^ (-(1 / 2 : ℝ))) ^ 2 * dilatedSource (1 / 2) (k + 1) n ^ 2 +
          (dilatedSource η (k + 1 + 1) n - dilatedSource (1 / 2) (k + 1 + 1) n) ^ 2 +
          (K' ^ (-η) - K' ^ (-(1 / 2 : ℝ))) ^ 2 * dilatedSource (1 / 2) (k + 1 + 1) n ^ 2) :=
        Finset.sum_le_sum hpt
    _ = 4 * (∑ n ∈ Finset.range T,
            (dilatedSource η (k + 1) n - dilatedSource (1 / 2) (k + 1) n) ^ 2 +
          (K ^ (-η) - K ^ (-(1 / 2 : ℝ))) ^ 2 *
            ∑ n ∈ Finset.range T, dilatedSource (1 / 2) (k + 1) n ^ 2 +
          ∑ n ∈ Finset.range T,
            (dilatedSource η (k + 1 + 1) n - dilatedSource (1 / 2) (k + 1 + 1) n) ^ 2 +
          (K' ^ (-η) - K' ^ (-(1 / 2 : ℝ))) ^ 2 *
            ∑ n ∈ Finset.range T, dilatedSource (1 / 2) (k + 1 + 1) n ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        have hK : (((k + 1 : ℕ) : ℝ)) = K := rfl
        have hK' : (((k + 1 + 1 : ℕ) : ℝ)) = K' := rfl
        rw [hK] at hE1 j2
        rw [hK'] at hE3 j4
        nlinarith

/-- **Every column converges in `ℓ²` as `η ↓ ½`.** -/
theorem column_l2_tendsto_half (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ η in 𝓝[>] (1 / 2 : ℝ), ∀ T : ℕ,
      ∑ n ∈ Finset.range T,
        (arithmeticDampingCenteredRow η n k - arithmeticDampingCenteredRow (1 / 2) n k) ^ 2 ≤ ε := by
  intro ε hε
  have hsum : Summable fun n => orbitCoord (1 / 2) n ^ 2 := by
    have h := (admits_iff_summable_orbit (by norm_num : (0 : ℝ) < 1 / 2)).mp
      (admits_dampedMobiusEnergy_of_half_le le_rfl)
    simpa only [centeredOperator_reciprocal_eq_orbitCoord] using h
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = ∑' n, orbitCoord (1 / 2) n ^ 2 := ⟨_, rfl⟩
  have hU0 : 0 ≤ U := by rw [hU]; exact tsum_nonneg fun n => sq_nonneg _
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ → ℝ, ρ = fun η => (RHTower.pmPowerDampedDivisorDensity η).re := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ((k + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = ((k + 1 + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  have hK'0 : 0 < K' := by rw [hK']; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 5 * ρ (1 / 2) ^ 2 + 2 * U := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (4 * (K + K') * (7 + B)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hρc : Tendsto ρ (𝓝[>] (1 / 2)) (𝓝 (ρ (1 / 2))) := by
    rw [hρ]; exact (continuousAt_density_re (by norm_num)).tendsto.mono_left nhdsWithin_le_nhds
  have hpowc : ∀ x : ℝ, 0 < x →
      Tendsto (fun η : ℝ => (x ^ (-η) - x ^ (-(1 / 2 : ℝ))) ^ 2) (𝓝[>] (1 / 2)) (𝓝 0) := by
    intro x hx
    have h : Tendsto (fun η : ℝ => x ^ (-η)) (𝓝[>] (1 / 2)) (𝓝 (x ^ (-(1 / 2 : ℝ)))) :=
      ((continuous_const.rpow continuous_neg fun _ => Or.inl hx.ne').tendsto _).mono_left
        nhdsWithin_le_nhds
    simpa using (h.sub_const (x ^ (-(1 / 2 : ℝ)))).pow 2
  have hρ2 : Tendsto (fun η => (ρ η - ρ (1 / 2)) ^ 2) (𝓝[>] (1 / 2)) (𝓝 0) := by
    simpa using (hρc.sub_const (ρ (1 / 2))).pow 2
  filter_upwards [hρ2.eventually (ge_mem_nhds hδ0), orbit_l2_tendsto_half δ hδ0,
    (hpowc K hK0).eventually (ge_mem_nhds hδ0), (hpowc K' hK'0).eventually (ge_mem_nhds hδ0),
    (self_mem_nhdsWithin : Ioi (1 / 2 : ℝ) ∈ 𝓝[>] (1 / 2))] with η h1 h2 h3 h4 h5 T
  have hη0 : 0 ≤ η := by have : (1 / 2 : ℝ) < η := h5; linarith
  have hbound := sum_sq_column_sub_le hη0 k T
  have hUT : ∑ m ∈ Finset.range T, orbitCoord (1 / 2) m ^ 2 ≤ U := by
    rw [hU]; exact hsum.sum_le_tsum _ fun m _ => sq_nonneg _
  rw [← hK, ← hK'] at hbound
  have hE : 5 * ((RHTower.pmPowerDampedDivisorDensity η).re -
      (RHTower.pmPowerDampedDivisorDensity (1 / 2)).re) ^ 2 +
      2 * ∑ m ∈ Finset.range T, (orbitCoord η m - orbitCoord (1 / 2) m) ^ 2 ≤ 7 * δ := by
    have := h2 T
    have h1' : ((RHTower.pmPowerDampedDivisorDensity η).re -
        (RHTower.pmPowerDampedDivisorDensity (1 / 2)).re) ^ 2 ≤ δ := by rw [hρ] at h1; exact h1
    linarith
  have hBT : 5 * (RHTower.pmPowerDampedDivisorDensity (1 / 2)).re ^ 2 +
      2 * ∑ m ∈ Finset.range T, orbitCoord (1 / 2) m ^ 2 ≤ B := by
    rw [hB, hρ]; linarith
  have hBT0 : 0 ≤ 5 * (RHTower.pmPowerDampedDivisorDensity (1 / 2)).re ^ 2 +
      2 * ∑ m ∈ Finset.range T, orbitCoord (1 / 2) m ^ 2 := by positivity
  have hd : (K ^ (-η) - K ^ (-(1 / 2 : ℝ))) ^ 2 * K + (K' ^ (-η) - K' ^ (-(1 / 2 : ℝ))) ^ 2 * K' ≤
      δ * (K + K') := by nlinarith
  have hd0 : 0 ≤ (K ^ (-η) - K ^ (-(1 / 2 : ℝ))) ^ 2 * K + (K' ^ (-η) - K' ^ (-(1 / 2 : ℝ))) ^ 2 * K' := by
    positivity
  have hfin : 4 * δ * (K + K') * (7 + B) = ε := by rw [hδ]; field_simp
  refine hbound.trans ?_
  have k1 := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ K + K')
  have k2 := mul_le_mul hd hBT hBT0 (by positivity)
  nlinarith

/-! ### Operator norm -/

/-- The tail `b · 1_{k ≥ K}` of a sequence in `c₀`. -/
def tailC0 (b : C₀(ℕ, ℝ)) (K : ℕ) : C₀(ℕ, ℝ) where
  toFun k := if K ≤ k then b k else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    refine squeeze_zero_norm (fun k => ?_) (by simpa using b.zero_at_infty'.norm)
    split_ifs
    · exact le_rfl
    · simp

theorem tailC0_apply (b : C₀(ℕ, ℝ)) (K k : ℕ) : tailC0 b K k = if K ≤ k then b k else 0 := rfl

/-- **The chain is norm-continuous at half damping**: for every `ε > 0`, eventually as `η ↓ ½`,
`Σ_{n<T} ((C_η − C_{½}) b)(n)² ≤ ε Σ_k b_k²` for every finitely supported `b` and every `T`. -/
theorem centeredOperator_norm_tendsto_half :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ η in 𝓝[>] (1 / 2 : ℝ), ∀ (hη : 0 < η) (b : C₀(ℕ, ℝ)) {N : ℕ},
      (∀ k, N ≤ k → b k = 0) → ∀ T : ℕ,
        ∑ n ∈ Finset.range T, (arithmeticDampingCenteredOperator hη b n -
          arithmeticDampingCenteredOperator (by norm_num : (0 : ℝ) < 1 / 2) b n) ^ 2 ≤
          ε * ∑ k ∈ Finset.range N, b k ^ 2 := by
  intro ε hε
  obtain ⟨M, K₁, hM, hunif⟩ := exists_centeredOperator_tail_l2_le_uniform
  obtain ⟨M', K₁', hM', hhalf⟩ := exists_centeredOperator_tail_l2_le_half
  -- a cut `K₀` beyond which both tails are small
  have hlim : Tendsto (fun K : ℕ => (M + M') * (K : ℝ) ^ (-(1 / 10 : ℝ))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop).const_mul (M + M')
    simpa using this
  obtain ⟨K₀, hK₀⟩ := ((hlim.eventually (gt_mem_nhds (by positivity : 0 < ε / 9))).and
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (max K₁ K₁')))).exists
  have hK₀1 : K₁ ≤ (K₀ : ℝ) := (le_max_left _ _).trans hK₀.2
  have hK₀2 : K₁' ≤ (K₀ : ℝ) := (le_max_right _ _).trans hK₀.2
  have hMt : M * (K₀ : ℝ) ^ (-(1 / 10 : ℝ)) ≤ ε / 9 := by
    have : 0 ≤ M' * (K₀ : ℝ) ^ (-(1 / 10 : ℝ)) := by positivity
    nlinarith [hK₀.1]
  have hMt' : M' * (K₀ : ℝ) ^ (-(1 / 10 : ℝ)) ≤ ε / 9 := by
    have : 0 ≤ M * (K₀ : ℝ) ^ (-(1 / 10 : ℝ)) := by positivity
    nlinarith [hK₀.1]
  -- the first `K₀` columns converge
  have hcols : ∀ᶠ η in 𝓝[>] (1 / 2 : ℝ), ∀ k ∈ Finset.range K₀, ∀ T : ℕ,
      ∑ n ∈ Finset.range T,
        (arithmeticDampingCenteredRow η n k - arithmeticDampingCenteredRow (1 / 2) n k) ^ 2 ≤
          ε / (9 * (K₀ + 1)) :=
    (Finset.range K₀).eventually_all.mpr fun k _ =>
      column_l2_tendsto_half k _ (by positivity)
  filter_upwards [hcols, Ioo_mem_nhdsGT (by norm_num : (1 / 2 : ℝ) < 1)] with η hc hη01 hη b N hb T
  have hnb0 : 0 ≤ ∑ k ∈ Finset.range N, b k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have happ : ∀ (η' : ℝ) (hη' : 0 < η') (n : ℕ), arithmeticDampingCenteredOperator hη' b n =
      ∑ k ∈ Finset.range N, arithmeticDampingCenteredRow η' n k * b k := by
    intro η' hη' n
    rw [arithmeticDampingCenteredOperator_apply]
    exact tsum_eq_sum fun k hk => by rw [hb k (by simpa using hk), mul_zero]
  have hbt : ∀ k, N ≤ k → tailC0 b K₀ k = 0 := fun k hk => by
    rw [tailC0_apply]; split_ifs <;> simp [hb k hk]
  have hbl : ∀ k, k < K₀ → tailC0 b K₀ k = 0 := fun k hk => by
    rw [tailC0_apply, if_neg (by omega)]
  have htail : ∀ (η' : ℝ) (hη' : 0 < η') (n : ℕ),
      arithmeticDampingCenteredOperator hη' (tailC0 b K₀) n =
        ∑ k ∈ Finset.range N, arithmeticDampingCenteredRow η' n k * (if K₀ ≤ k then b k else 0) := by
    intro η' hη' n
    rw [arithmeticDampingCenteredOperator_apply]
    exact tsum_eq_sum fun k hk => by rw [hbt k (by simpa using hk), mul_zero]
  -- the tail energy is at most the energy of `b`
  have hnbt : ∑ k ∈ Finset.range N, tailC0 b K₀ k ^ 2 ≤ ∑ k ∈ Finset.range N, b k ^ 2 :=
    Finset.sum_le_sum fun k _ => by rw [tailC0_apply]; split_ifs <;> simp [sq_nonneg]
  have hT1 := hunif η hη01.1 hη01.2 (tailC0 b K₀) hK₀1 hbt hbl T
  have hT2 := hhalf (tailC0 b K₀) hK₀2 hbt hbl T
  -- head: Cauchy–Schwarz over the first `K₀` columns
  set D : ℕ → ℕ → ℝ := fun n k =>
    arithmeticDampingCenteredRow η n k - arithmeticDampingCenteredRow (1 / 2) n k
  set H : ℕ → ℝ := fun n => ∑ k ∈ Finset.range K₀, D n k * (if k < N then b k else 0)
  have hsplit : ∀ n, arithmeticDampingCenteredOperator hη b n -
      arithmeticDampingCenteredOperator (by norm_num : (0 : ℝ) < 1 / 2) b n =
      H n + arithmeticDampingCenteredOperator hη (tailC0 b K₀) n -
        arithmeticDampingCenteredOperator (by norm_num : (0 : ℝ) < 1 / 2) (tailC0 b K₀) n := by
    intro n
    rw [happ η hη, happ (1 / 2) (by norm_num), htail η hη, htail (1 / 2) (by norm_num),
      add_sub_assoc, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    simp only [H, D]
    -- split the moduli at `K₀`
    have hrw : ∀ k ∈ Finset.range N, arithmeticDampingCenteredRow η n k * b k -
        arithmeticDampingCenteredRow (1 / 2) n k * b k =
        (if k < K₀ then D n k * b k else 0) +
          (arithmeticDampingCenteredRow η n k * (if K₀ ≤ k then b k else 0) -
            arithmeticDampingCenteredRow (1 / 2) n k * (if K₀ ≤ k then b k else 0)) := by
      intro k _
      simp only [D]
      split_ifs with h1 h2 <;> first | omega | ring
    rw [Finset.sum_congr rfl hrw, Finset.sum_add_distrib]
    congr 1
    -- `Σ_{k<N} 1_{k<K₀} D b = Σ_{k<K₀} 1_{k<N} D b`
    rw [← Finset.sum_filter]
    have hfil : (Finset.range N).filter (fun k => k < K₀) = (Finset.range K₀).filter (fun k => k < N) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range]; exact and_comm
    rw [hfil, Finset.sum_filter]
    exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp [D]
  have hH : ∑ n ∈ Finset.range T, H n ^ 2 ≤ ε / 9 * ∑ k ∈ Finset.range N, b k ^ 2 := by
    have hbK : ∑ k ∈ Finset.range K₀, (if k < N then b k else 0) ^ 2 ≤
        ∑ k ∈ Finset.range N, b k ^ 2 := by
      rw [show ∑ k ∈ Finset.range K₀, (if k < N then b k else 0) ^ 2 =
          ∑ k ∈ Finset.range (min K₀ N), b k ^ 2 by
        rw [← Finset.sum_range_add_sum_Ico _ (min_le_left K₀ N)]
        rw [Finset.sum_eq_zero (s := Finset.Ico (min K₀ N) K₀) fun k hk => by
          simp only [Finset.mem_Ico] at hk
          rw [if_neg (by omega)]; ring, add_zero]
        exact Finset.sum_congr rfl fun k hk => by
          simp only [Finset.mem_range] at hk; rw [if_pos (by omega)]]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (min_le_right K₀ N)) fun k _ _ => sq_nonneg _
    have hcs : ∀ n, H n ^ 2 ≤ (∑ k ∈ Finset.range K₀, D n k ^ 2) *
        ∑ k ∈ Finset.range K₀, (if k < N then b k else 0) ^ 2 := fun n =>
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.range K₀) (fun k => D n k)
        (fun k => if k < N then b k else 0)
    have hcol : ∑ k ∈ Finset.range K₀, ∑ n ∈ Finset.range T, D n k ^ 2 ≤ ε / 9 := by
      calc ∑ k ∈ Finset.range K₀, ∑ n ∈ Finset.range T, D n k ^ 2
          ≤ ∑ k ∈ Finset.range K₀, ε / (9 * (K₀ + 1)) :=
            Finset.sum_le_sum fun k hk => hc k hk T
        _ = K₀ * (ε / (9 * (K₀ + 1))) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ ε / 9 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    calc ∑ n ∈ Finset.range T, H n ^ 2
        ≤ ∑ n ∈ Finset.range T, (∑ k ∈ Finset.range K₀, D n k ^ 2) *
            ∑ k ∈ Finset.range N, b k ^ 2 :=
          Finset.sum_le_sum fun n _ => (hcs n).trans
            (mul_le_mul_of_nonneg_left hbK (Finset.sum_nonneg fun k _ => sq_nonneg _))
      _ = (∑ k ∈ Finset.range K₀, ∑ n ∈ Finset.range T, D n k ^ 2) *
            ∑ k ∈ Finset.range N, b k ^ 2 := by
          rw [← Finset.sum_mul, Finset.sum_comm]
      _ ≤ ε / 9 * ∑ k ∈ Finset.range N, b k ^ 2 := mul_le_mul_of_nonneg_right hcol hnb0
  -- assemble: `(H + t − t')² ≤ 3 (H² + t² + t'²)`
  calc ∑ n ∈ Finset.range T, (arithmeticDampingCenteredOperator hη b n -
        arithmeticDampingCenteredOperator (by norm_num : (0 : ℝ) < 1 / 2) b n) ^ 2
      ≤ ∑ n ∈ Finset.range T, 3 * (H n ^ 2 +
          arithmeticDampingCenteredOperator hη (tailC0 b K₀) n ^ 2 +
          arithmeticDampingCenteredOperator (by norm_num : (0 : ℝ) < 1 / 2) (tailC0 b K₀) n ^ 2) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [hsplit n]
        nlinarith [sq_nonneg (H n - arithmeticDampingCenteredOperator hη (tailC0 b K₀) n),
          sq_nonneg (H n + arithmeticDampingCenteredOperator
            (by norm_num : (0 : ℝ) < 1 / 2) (tailC0 b K₀) n),
          sq_nonneg (arithmeticDampingCenteredOperator hη (tailC0 b K₀) n +
            arithmeticDampingCenteredOperator (by norm_num : (0 : ℝ) < 1 / 2) (tailC0 b K₀) n)]
    _ = 3 * (∑ n ∈ Finset.range T, H n ^ 2 +
          ∑ n ∈ Finset.range T, arithmeticDampingCenteredOperator hη (tailC0 b K₀) n ^ 2 +
          ∑ n ∈ Finset.range T,
            arithmeticDampingCenteredOperator (by norm_num : (0 : ℝ) < 1 / 2) (tailC0 b K₀) n ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ 3 * (ε / 9 * ∑ k ∈ Finset.range N, b k ^ 2 +
          ε / 9 * ∑ k ∈ Finset.range N, b k ^ 2 + ε / 9 * ∑ k ∈ Finset.range N, b k ^ 2) := by
        have t1 := hT1.trans (mul_le_mul hMt hnbt (Finset.sum_nonneg fun k _ => sq_nonneg _)
          (by positivity))
        have t2 := hT2.trans (mul_le_mul hMt' hnbt (Finset.sum_nonneg fun k _ => sq_nonneg _)
          (by positivity))
        linarith
    _ = ε * ∑ k ∈ Finset.range N, b k ^ 2 := by ring

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
