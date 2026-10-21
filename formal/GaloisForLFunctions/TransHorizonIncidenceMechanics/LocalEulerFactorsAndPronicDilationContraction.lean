import GaloisForLFunctions.TransHorizonIncidenceMechanics.CharacterFourParityRowsAtEveryHorizon

/-!
# Local Euler factors and the pronic dilation contraction

The pronic weight `1/(n(n+1))` contracts the prime dilation exactly at the critical exponent:
grouping the cells `n = pk + r`, `r < p`,

`Σ_{n ≤ T} f(⌊n/p⌋)²/(n(n+1)) ≤ p^{-1} Σ_{k ≤ T} f(k)²/(k(k+1))`,

because `Σ_{r<p} 1/((pk+r)(pk+r+1)) = 1/(pk(k+1))`. Multiplying a weight by the local Euler factor
`1 - a p^{-s}`, i.e. `c' = c ⋆ (δ₁ - a δ_p)`, acts on the receiver prefix along the dilation
`k ↦ pk`:

`A_{c'}(n) = A_c(n) - a A_c(⌊n/p⌋) + a m {n/p}`.

Hence `‖A_{c'}‖ ≤ (1 + |a| p^{-1/2}) ‖A_c‖ + |am|` always, and `(1 - |a| p^{-1/2}) ‖A_c‖ ≤ ‖A_{c'}‖ + |am|`.
**The receiver growth class is invariant under every local factor whose zero lies left of the
critical line** (`|a| < √p`, the zero of `1 - a p^{-s}` has real part `log_p |a| < 1/2`). The
threshold is sharp: the geometric weight `c(p^k) = p^{k/2}` diverges while
`c ⋆ (δ₁ - √p δ_p) = δ₁` has zero receiver energy.

For a weight that is multiplicative along `p` (`c(pd) = x c(d)`), the parity flip
`c^{(p)}(d) = (-1)^{v_p(d)} c(d)` satisfies `c^{(p)} ⋆ (δ₁ + x δ_p) = c ⋆ (δ₁ - x δ_p)`; for
`|x| < √p` flipping the parity at one prime, hence at finitely many, never changes the growth class.
A parity pair needs infinitely many flipped primes.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The pronic norm -/

/-- The pronic norm `‖f‖_T = (Σ_{n ≤ T} f(n)²/(n(n+1)))^{1/2}`. -/
def pronicNorm (f : ℕ → ℝ) (T : ℕ) : ℝ :=
  Real.sqrt (∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))

private theorem pronicSum_nonneg (f : ℕ → ℝ) (T : ℕ) :
    0 ≤ ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
  sum_nonneg fun n _ => by positivity

theorem pronicNorm_nonneg (f : ℕ → ℝ) (T : ℕ) : 0 ≤ pronicNorm f T := Real.sqrt_nonneg _

theorem weightPronicEnergy_eq_sq_pronicNorm (c : ℕ → ℝ) (m : ℝ) (T : ℕ) :
    weightPronicEnergy c m T = pronicNorm (weightCenteredPrefix c m) T ^ 2 := by
  rw [pronicNorm, Real.sq_sqrt (pronicSum_nonneg _ T)]
  rfl

/-- Minkowski's inequality for the pronic norm. -/
theorem pronicNorm_add_le (f g : ℕ → ℝ) (T : ℕ) :
    pronicNorm (fun n => f n + g n) T ≤ pronicNorm f T + pronicNorm g T := by
  set w : ℕ → ℝ := fun n => 1 / ((n : ℝ) * ((n : ℝ) + 1))
  have hw : ∀ n, 0 ≤ w n := fun n => by positivity
  have hsq : ∀ (h : ℕ → ℝ), ∑ n ∈ Icc 1 T, h n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      ∑ n ∈ Icc 1 T, (h n * Real.sqrt (w n)) ^ 2 := fun h => by
    refine sum_congr rfl fun n _ => ?_
    rw [mul_pow, Real.sq_sqrt (hw n)]
    simp only [w]; ring
  set F := pronicNorm f T
  set G := pronicNorm g T
  have hcs : ∑ n ∈ Icc 1 T, (f n * Real.sqrt (w n)) * (g n * Real.sqrt (w n)) ≤ F * G := by
    have h := sum_mul_sq_le_sq_mul_sq (Icc 1 T) (fun n => f n * Real.sqrt (w n))
      (fun n => g n * Real.sqrt (w n))
    have hF : F ^ 2 = ∑ n ∈ Icc 1 T, (f n * Real.sqrt (w n)) ^ 2 := by
      simp only [F, pronicNorm]; rw [Real.sq_sqrt (pronicSum_nonneg _ T), hsq]
    have hG : G ^ 2 = ∑ n ∈ Icc 1 T, (g n * Real.sqrt (w n)) ^ 2 := by
      simp only [G, pronicNorm]; rw [Real.sq_sqrt (pronicSum_nonneg _ T), hsq]
    rw [← hF, ← hG, ← mul_pow] at h
    exact (abs_le_of_sq_le_sq' h (mul_nonneg (pronicNorm_nonneg _ _) (pronicNorm_nonneg _ _))).2
  have hF : F ^ 2 = ∑ n ∈ Icc 1 T, (f n * Real.sqrt (w n)) ^ 2 := by
    simp only [F, pronicNorm]; rw [Real.sq_sqrt (pronicSum_nonneg _ T), hsq]
  have hG : G ^ 2 = ∑ n ∈ Icc 1 T, (g n * Real.sqrt (w n)) ^ 2 := by
    simp only [G, pronicNorm]; rw [Real.sq_sqrt (pronicSum_nonneg _ T), hsq]
  unfold pronicNorm
  rw [hsq]
  refine Real.sqrt_le_iff.mpr ⟨add_nonneg (pronicNorm_nonneg _ _) (pronicNorm_nonneg _ _), ?_⟩
  have hexp : ∑ n ∈ Icc 1 T, ((f n + g n) * Real.sqrt (w n)) ^ 2 =
      ∑ n ∈ Icc 1 T, (f n * Real.sqrt (w n)) ^ 2 +
        2 * ∑ n ∈ Icc 1 T, (f n * Real.sqrt (w n)) * (g n * Real.sqrt (w n)) +
          ∑ n ∈ Icc 1 T, (g n * Real.sqrt (w n)) ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hexp, ← hF, ← hG]
  nlinarith

theorem pronicNorm_smul (a : ℝ) (f : ℕ → ℝ) (T : ℕ) :
    pronicNorm (fun n => a * f n) T = |a| * pronicNorm f T := by
  unfold pronicNorm
  rw [← Real.sqrt_sq (abs_nonneg a), ← Real.sqrt_mul (sq_nonneg _), mul_sum]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [sq_abs]; ring

/-- `Σ_{n ≤ T} 1/(n(n+1)) = 1 - 1/(T+1)`. -/
theorem sum_Icc_pronic_eq (T : ℕ) :
    ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) = 1 - 1 / ((T : ℝ) + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    have h1 : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    field_simp
    ring

theorem pronicNorm_le_of_abs_le {f : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ n, |f n| ≤ B) (T : ℕ) :
    pronicNorm f T ≤ B := by
  unfold pronicNorm
  refine Real.sqrt_le_iff.mpr ⟨hB, ?_⟩
  have htel : ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ 1 := by
    rw [sum_Icc_pronic_eq]
    have : 0 ≤ 1 / ((T : ℝ) + 1) := by positivity
    linarith
  calc ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
      ≤ ∑ n ∈ Icc 1 T, B ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        refine sum_le_sum fun n hn => ?_
        rw [mul_one_div]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h n) 2
    _ = B ^ 2 * ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by rw [mul_sum]
    _ ≤ B ^ 2 * 1 := mul_le_mul_of_nonneg_left htel (sq_nonneg B)
    _ = B ^ 2 := mul_one _

/-! ### The dilation contraction -/

/-- One dilation block: `Σ_{r<p} 1/((pk+r)(pk+r+1)) = 1/(pk(k+1))` for `k ≥ 1`. -/
private theorem sum_block_pronic {p k : ℕ} (hp : 1 ≤ p) (hk : 1 ≤ k) :
    ∑ r ∈ range p, 1 / (((p * k + r : ℕ) : ℝ) * (((p * k + r : ℕ) : ℝ) + 1)) =
      1 / ((p : ℝ) * ((k : ℝ) * ((k : ℝ) + 1))) := by
  have htel : ∀ R : ℕ, ∑ r ∈ range R, 1 / (((p * k + r : ℕ) : ℝ) * (((p * k + r : ℕ) : ℝ) + 1)) =
      1 / ((p * k : ℕ) : ℝ) - 1 / ((p * k + R : ℕ) : ℝ) := by
    intro R
    induction R with
    | zero => simp
    | succ R ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : (0 : ℝ) < ((p * k + R : ℕ) : ℝ) := by
        exact_mod_cast (by nlinarith : 0 < p * k + R)
      push_cast at h1 ⊢
      field_simp
      ring
  rw [htel]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  push_cast
  field_simp
  ring

/-- **The pronic dilation contraction.** For `f(0) = 0` and `p ≥ 1`,
`Σ_{n ≤ T} f(⌊n/p⌋)²/(n(n+1)) ≤ p^{-1} Σ_{k ≤ T} f(k)²/(k(k+1))`. -/
theorem sum_pronic_dilate_le (f : ℕ → ℝ) (hf0 : f 0 = 0) {p : ℕ} (hp : 1 ≤ p) (T : ℕ) :
    ∑ n ∈ Icc 1 T, f (n / p) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (1 / (p : ℝ)) * ∑ k ∈ Icc 1 T, f k ^ 2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
  set g : ℕ → ℝ := fun n => f (n / p) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
  have hg0 : ∀ n, 0 ≤ g n := fun n => by positivity
  -- blocks
  have hblocks : ∀ J : ℕ, ∑ n ∈ range (p * J), g n =
      ∑ k ∈ range J, f k ^ 2 * (if k = 0 then 0 else 1 / ((p : ℝ) * ((k : ℝ) * ((k : ℝ) + 1)))) := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [show p * (J + 1) = p * J + p by ring, Finset.sum_range_add, ih, Finset.sum_range_succ]
      congr 1
      have hdiv : ∀ r ∈ range p, (p * J + r) / p = J := fun r hr => by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (mem_range.mp hr),
          zero_add]
      have hterm : ∀ r ∈ range p, g (p * J + r) =
          f J ^ 2 * (1 / (((p * J + r : ℕ) : ℝ) * (((p * J + r : ℕ) : ℝ) + 1))) := fun r hr => by
        simp only [g, hdiv r hr]; ring
      rw [sum_congr rfl hterm, ← mul_sum]
      split_ifs with hJ
      · subst hJ; simp [hf0]
      · congr 1
        exact sum_block_pronic hp (Nat.one_le_iff_ne_zero.mpr hJ)
  have hsub : ∑ n ∈ Icc 1 T, g n ≤ ∑ n ∈ range (p * (T / p + 1)), g n := by
    refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => hg0 n
    rw [mem_range]
    have := Nat.lt_mul_div_succ T (show 0 < p by omega)
    rw [mem_Icc] at hn
    omega
  have hright : ∑ k ∈ range (T / p + 1),
      f k ^ 2 * (if k = 0 then 0 else 1 / ((p : ℝ) * ((k : ℝ) * ((k : ℝ) + 1))))
      ≤ (1 / (p : ℝ)) * ∑ k ∈ Icc 1 T, f k ^ 2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
    rw [dampedSign_sum_range_succ_eq_add_Icc, if_pos rfl, mul_zero, zero_add, mul_sum]
    calc ∑ k ∈ Icc 1 (T / p), f k ^ 2 * (if k = 0 then 0 else 1 / ((p : ℝ) * ((k : ℝ) * ((k : ℝ) + 1))))
        = ∑ k ∈ Icc 1 (T / p), 1 / (p : ℝ) * (f k ^ 2 / ((k : ℝ) * ((k : ℝ) + 1))) := by
          refine sum_congr rfl fun k hk => ?_
          rw [if_neg (by have := (mem_Icc.mp hk).1; omega)]
          field_simp
      _ ≤ ∑ k ∈ Icc 1 T, 1 / (p : ℝ) * (f k ^ 2 / ((k : ℝ) * ((k : ℝ) + 1))) := by
          refine sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (Nat.div_le_self T p))
            fun k _ _ => by positivity
  calc ∑ n ∈ Icc 1 T, g n ≤ ∑ n ∈ range (p * (T / p + 1)), g n := hsub
    _ = _ := hblocks (T / p + 1)
    _ ≤ _ := hright

theorem pronicNorm_dilate_le (f : ℕ → ℝ) (hf0 : f 0 = 0) {p : ℕ} (hp : 1 ≤ p) (T : ℕ) :
    pronicNorm (fun n => f (n / p)) T ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) * pronicNorm f T := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  unfold pronicNorm
  have hpow : (p : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt (1 / (p : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow zero_le_one hp0.le, Real.one_rpow, Real.rpow_neg hp0.le,
      inv_eq_one_div]
  rw [hpow, ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt (sum_pronic_dilate_le f hf0 hp T)

/-! ### Local Euler factors -/

/-- `c ⋆ (δ₁ - a δ_p)`: the weight multiplied by the local factor `1 - a p^{-s}`. -/
def localFactorWeight (c : ℕ → ℝ) (p : ℕ) (a : ℝ) (d : ℕ) : ℝ :=
  c d - a * (if p ∣ d then c (d / p) else 0)

/-- The floor sums `S_c(n) = Σ_{d ≤ n} c(d)⌊n/d⌋` obey `S_{c'}(n) = S_c(n) - a S_c(⌊n/p⌋)`. -/
theorem floorSum_localFactorWeight (c : ℕ → ℝ) {p : ℕ} (hp : 1 ≤ p) (a : ℝ) (n : ℕ) :
    ∑ d ∈ Icc 1 n, localFactorWeight c p a d * ((n / d : ℕ) : ℝ) =
      ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) -
        a * ∑ k ∈ Icc 1 (n / p), c k * ((n / p / k : ℕ) : ℝ) := by
  unfold localFactorWeight
  simp_rw [sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum, ite_mul, zero_mul]
  congr 2
  rw [← sum_filter, RHTower.sum_Icc_filter_dvd_reindex p n (by omega)]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.mul_div_cancel_left k (by omega), Nat.div_div_eq_div_mul]

/-- The mean of a local-factor weight: `Σ c'(d)/d = m - a m/p`. -/
theorem hasSum_localFactorWeight_div {c : ℕ → ℝ} {m : ℝ} (hm : HasSum (fun d : ℕ => c d / d) m)
    {p : ℕ} (hp : 1 ≤ p) (a : ℝ) :
    HasSum (fun d : ℕ => localFactorWeight c p a d / d) (m - a * (m / p)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  set f : ℕ → ℝ := fun d => (if p ∣ d then c (d / p) else 0) / d
  have hinj : Function.Injective (fun k : ℕ => p * k) :=
    fun a b h => Nat.eq_of_mul_eq_mul_left (by omega) h
  have hoff : ∀ x, x ∉ Set.range (fun k : ℕ => p * k) → f x = 0 := by
    intro x hx
    simp only [f]
    rw [if_neg (fun h => hx (by obtain ⟨k, rfl⟩ := h; exact ⟨k, rfl⟩)), zero_div]
  have hcomp : (f ∘ fun k : ℕ => p * k) = fun k => c k / k / p := by
    funext k
    simp only [f, Function.comp_apply, if_pos (dvd_mul_right p k),
      Nat.mul_div_cancel_left k (by omega : 0 < p), Nat.cast_mul]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp
  have hf : HasSum f (m / p) := by
    rw [← hinj.hasSum_iff hoff, hcomp]
    exact hm.div_const _
  refine (hm.sub (hf.mul_left a)).congr_fun fun d => ?_
  simp only [localFactorWeight, f]
  ring

/-- **The local factor acts on the receiver along the dilation `k ↦ pk`:**
`A_{c'}(n) = A_c(n) - a A_c(⌊n/p⌋) + a m (n/p - ⌊n/p⌋)`. -/
theorem weightCenteredPrefix_localFactorWeight (c : ℕ → ℝ) (m : ℝ) {p : ℕ} (hp : 1 ≤ p) (a : ℝ)
    (n : ℕ) :
    weightCenteredPrefix (localFactorWeight c p a) (m - a * (m / p)) n =
      weightCenteredPrefix c m n - a * weightCenteredPrefix c m (n / p) +
        a * m * ((n : ℝ) / p - ((n / p : ℕ) : ℝ)) := by
  simp only [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor]
  rw [floorSum_localFactorWeight c hp a n]
  ring

/-- **Forward bound:** `‖A_{c'}‖ ≤ (1 + |a| p^{-1/2}) ‖A_c‖ + |am|`, for every `a`. -/
theorem pronicNorm_localFactor_le (c : ℕ → ℝ) (m : ℝ) {p : ℕ} (hp : 1 ≤ p) (a : ℝ) (T : ℕ) :
    pronicNorm (weightCenteredPrefix (localFactorWeight c p a) (m - a * (m / p))) T ≤
      (1 + |a| * (p : ℝ) ^ (-(1 / 2 : ℝ))) * pronicNorm (weightCenteredPrefix c m) T + |a * m| := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set A := weightCenteredPrefix c m
  have hA0 : A 0 = 0 := by simp [A, weightCenteredPrefix]
  have hfrac : ∀ n : ℕ, |a * m * ((n : ℝ) / p - ((n / p : ℕ) : ℝ))| ≤ |a * m| := by
    intro n
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    have h1 : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / p := Nat.cast_div_le
    have h2 : (n : ℝ) / p - 1 < ((n / p : ℕ) : ℝ) := by
      have h := Nat.lt_div_mul_add (a := n) (show 0 < p by omega)
      have h' : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
      rw [div_sub_one hp0.ne', div_lt_iff₀ hp0]; linarith
    rw [abs_le]; constructor <;> linarith
  have hid := weightCenteredPrefix_localFactorWeight c m hp a
  calc pronicNorm (weightCenteredPrefix (localFactorWeight c p a) (m - a * (m / p))) T
      = pronicNorm (fun n => (A n + (-a) * A (n / p)) +
          a * m * ((n : ℝ) / p - ((n / p : ℕ) : ℝ))) T := by
        unfold pronicNorm; congr 1; refine sum_congr rfl fun n _ => ?_; rw [hid]; ring
    _ ≤ pronicNorm (fun n => A n + (-a) * A (n / p)) T +
          pronicNorm (fun n => a * m * ((n : ℝ) / p - ((n / p : ℕ) : ℝ))) T :=
        pronicNorm_add_le _ _ T
    _ ≤ (pronicNorm A T + pronicNorm (fun n => (-a) * A (n / p)) T) + |a * m| :=
        add_le_add (pronicNorm_add_le _ _ T) (pronicNorm_le_of_abs_le (abs_nonneg _) hfrac T)
    _ ≤ (pronicNorm A T + |a| * ((p : ℝ) ^ (-(1 / 2 : ℝ)) * pronicNorm A T)) + |a * m| := by
        rw [pronicNorm_smul (-a) (fun n => A (n / p)), abs_neg]
        gcongr
        exact pronicNorm_dilate_le A hA0 hp T
    _ = _ := by ring

/-- **Backward bound:** `(1 - |a| p^{-1/2}) ‖A_c‖ ≤ ‖A_{c'}‖ + |am|`. -/
theorem pronicNorm_le_of_localFactor (c : ℕ → ℝ) (m : ℝ) {p : ℕ} (hp : 1 ≤ p) (a : ℝ) (T : ℕ) :
    (1 - |a| * (p : ℝ) ^ (-(1 / 2 : ℝ))) * pronicNorm (weightCenteredPrefix c m) T ≤
      pronicNorm (weightCenteredPrefix (localFactorWeight c p a) (m - a * (m / p))) T + |a * m| := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set A := weightCenteredPrefix c m
  set A' := weightCenteredPrefix (localFactorWeight c p a) (m - a * (m / p))
  have hA0 : A 0 = 0 := by simp [A, weightCenteredPrefix]
  have hid := weightCenteredPrefix_localFactorWeight c m hp a
  have hfrac : ∀ n : ℕ, |(-(a * m)) * ((n : ℝ) / p - ((n / p : ℕ) : ℝ))| ≤ |a * m| := by
    intro n
    rw [abs_mul, abs_neg]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    have h1 : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / p := Nat.cast_div_le
    have h2 : (n : ℝ) / p - 1 < ((n / p : ℕ) : ℝ) := by
      have h := Nat.lt_div_mul_add (a := n) (show 0 < p by omega)
      have h' : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
      rw [div_sub_one hp0.ne', div_lt_iff₀ hp0]; linarith
    rw [abs_le]; constructor <;> linarith
  have hback : pronicNorm A T ≤ pronicNorm A' T + |a| * ((p : ℝ) ^ (-(1 / 2 : ℝ)) * pronicNorm A T)
      + |a * m| := by
    calc pronicNorm A T = pronicNorm (fun n => (A' n + a * A (n / p)) +
          (-(a * m)) * ((n : ℝ) / p - ((n / p : ℕ) : ℝ))) T := by
          unfold pronicNorm; congr 1; refine sum_congr rfl fun n _ => ?_
          simp only [A', hid]; ring
      _ ≤ pronicNorm (fun n => A' n + a * A (n / p)) T +
            pronicNorm (fun n => (-(a * m)) * ((n : ℝ) / p - ((n / p : ℕ) : ℝ))) T :=
          pronicNorm_add_le _ _ T
      _ ≤ (pronicNorm A' T + pronicNorm (fun n => a * A (n / p)) T) + |a * m| :=
          add_le_add (pronicNorm_add_le _ _ T) (pronicNorm_le_of_abs_le (abs_nonneg _) hfrac T)
      _ ≤ _ := by
          rw [pronicNorm_smul a (fun n => A (n / p))]
          gcongr
          exact pronicNorm_dilate_le A hA0 hp T
  nlinarith

/-- **Local factors left of the critical line preserve the growth class.** For `|a| < √p`, the
receiver energy of `c` is bounded iff that of `c ⋆ (δ₁ - a δ_p)` is. -/
theorem bounded_weightPronicEnergy_localFactor_iff (c : ℕ → ℝ) (m : ℝ) {p : ℕ} (hp : 1 ≤ p)
    {a : ℝ} (ha : |a| < Real.sqrt p) :
    (∃ B, ∀ T, weightPronicEnergy c m T ≤ B) ↔
      (∃ B, ∀ T, weightPronicEnergy (localFactorWeight c p a) (m - a * (m / p)) T ≤ B) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq : |a| * (p : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
    rw [Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow, mul_inv_lt_iff₀ (Real.sqrt_pos.mpr hp0), one_mul]
    exact ha
  have hq0 : 0 ≤ |a| * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  simp_rw [weightPronicEnergy_eq_sq_pronicNorm]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨((1 + |a| * (p : ℝ) ^ (-(1 / 2 : ℝ))) * Real.sqrt (max B 0) + |a * m|) ^ 2, fun T => ?_⟩
    have hN : pronicNorm (weightCenteredPrefix c m) T ≤ Real.sqrt (max B 0) :=
      Real.le_sqrt_of_sq_le ((hB T).trans (le_max_left _ _))
    refine pow_le_pow_left₀ (pronicNorm_nonneg _ _) ((pronicNorm_localFactor_le c m hp a T).trans ?_) 2
    gcongr
  · rintro ⟨B, hB⟩
    refine ⟨((Real.sqrt (max B 0) + |a * m|) / (1 - |a| * (p : ℝ) ^ (-(1 / 2 : ℝ)))) ^ 2,
      fun T => ?_⟩
    have hN : pronicNorm (weightCenteredPrefix (localFactorWeight c p a) (m - a * (m / p))) T ≤
        Real.sqrt (max B 0) := Real.le_sqrt_of_sq_le ((hB T).trans (le_max_left _ _))
    refine pow_le_pow_left₀ (pronicNorm_nonneg _ _) ?_ 2
    rw [le_div_iff₀ (by linarith)]
    have := pronicNorm_le_of_localFactor c m hp a T
    nlinarith

/-! ### Sharpness at the critical line -/

/-- The geometric weight `g(p^k) = p^{k/2}`, zero off the powers of `p`. -/
def criticalGeometricWeight (p : ℕ) (d : ℕ) : ℝ :=
  if d ≠ 0 ∧ d = p ^ d.factorization p then Real.sqrt p ^ d.factorization p else 0

theorem criticalGeometricWeight_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    criticalGeometricWeight p (p ^ k) = Real.sqrt p ^ k := by
  have hfac : (p ^ k).factorization p = k := by
    rw [Nat.Prime.factorization_pow hp]; simp
  unfold criticalGeometricWeight
  rw [hfac, if_pos ⟨pow_ne_zero _ hp.ne_zero, rfl⟩]

theorem criticalGeometricWeight_eq_zero {p : ℕ} {d : ℕ} (hd : ∀ k, d ≠ p ^ k) :
    criticalGeometricWeight p d = 0 := by
  unfold criticalGeometricWeight
  rw [if_neg]
  rintro ⟨-, h⟩
  exact hd _ h

/-- At the critical line the local factor kills the geometric weight:
`g ⋆ (δ₁ - √p δ_p) = δ₁`. -/
theorem localFactorWeight_criticalGeometricWeight {p : ℕ} (hp : p.Prime) (d : ℕ) :
    localFactorWeight (criticalGeometricWeight p) p (Real.sqrt p) d = if d = 1 then 1 else 0 := by
  unfold localFactorWeight
  by_cases hpow : ∃ k, d = p ^ k
  · obtain ⟨k, rfl⟩ := hpow
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [pow_zero, if_neg hp.not_dvd_one, if_true, mul_zero, sub_zero]
      simpa using criticalGeometricWeight_pow hp 0
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hne : p ^ (j + 1) ≠ 1 := (Nat.one_lt_pow (by omega) hp.one_lt).ne'
      rw [if_pos (dvd_pow_self p (by omega)), pow_succ, Nat.mul_div_cancel _ hp.pos, ← pow_succ,
        criticalGeometricWeight_pow hp, criticalGeometricWeight_pow hp, if_neg hne, pow_succ]
      ring
  · push Not at hpow
    have hd1 : d ≠ 1 := fun h => hpow 0 (by simp [h])
    rw [criticalGeometricWeight_eq_zero hpow, if_neg hd1]
    split_ifs with hdvd
    · obtain ⟨e, rfl⟩ := hdvd
      have he : ∀ k, e ≠ p ^ k := fun k h => hpow (k + 1) (by rw [h, pow_succ, mul_comm])
      rw [Nat.mul_div_cancel_left e hp.pos, criticalGeometricWeight_eq_zero he]
      ring
    · ring

theorem hasSum_criticalGeometricWeight_div {p : ℕ} (hp : p.Prime) :
    HasSum (fun d : ℕ => criticalGeometricWeight p d / d) (1 / (1 - (Real.sqrt p)⁻¹)) := by
  have hp1 : (1 : ℝ) < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast hp.one_lt)
  have hr : (Real.sqrt p)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hr0 : 0 ≤ (Real.sqrt p)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hinj : Function.Injective (fun k : ℕ => p ^ k) := Nat.pow_right_injective hp.two_le
  have hoff : ∀ x, x ∉ Set.range (fun k : ℕ => p ^ k) → criticalGeometricWeight p x / x = 0 := by
    intro x hx
    rw [criticalGeometricWeight_eq_zero fun k h => hx ⟨k, h.symm⟩, zero_div]
  rw [← hinj.hasSum_iff hoff]
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
  have hfun : ((fun d : ℕ => criticalGeometricWeight p d / d) ∘ fun k : ℕ => p ^ k) =
      fun k => (Real.sqrt p)⁻¹ ^ k := by
    funext k
    have hpk : ((p : ℝ)) ^ k = (Real.sqrt p ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg p)]
    simp only [Function.comp_apply, criticalGeometricWeight_pow hp, Nat.cast_pow]
    rw [hpk, inv_pow]
    have : Real.sqrt p ^ k ≠ 0 := pow_ne_zero _ (by linarith)
    field_simp
  rw [hfun, one_div]
  exact hasSum_geometric_of_lt_one hr0 hr

/-- **The drift on a window.** For `c ≥ 0`, `Σ c(d)/d = m` and `n ≤ X`:
`A_c(n) ≤ -n Σ_{n < d ≤ X} c(d)/d`. -/
theorem weightCenteredPrefix_le_neg_window_drift {c : ℕ → ℝ} {m : ℝ} (hc : ∀ d, 0 ≤ c d)
    (hm : HasSum (fun d : ℕ => c d / d) m) {n X : ℕ} (hnX : n ≤ X) :
    weightCenteredPrefix c m n ≤ -((n : ℝ) * ∑ d ∈ Ioc n X, c d / d) := by
  have hfloor : ∑ d ∈ Icc 1 n, c d * ((n / d : ℕ) : ℝ) ≤ (n : ℝ) * ∑ d ∈ Ioc 0 n, c d / d := by
    have h1 : Icc 1 n = Ioc 0 n := by ext d; simp only [mem_Icc, mem_Ioc]; omega
    rw [mul_sum, ← h1]
    refine sum_le_sum fun d _ => ?_
    have := Nat.cast_div_le (α := ℝ) (m := n) (n := d)
    calc c d * ((n / d : ℕ) : ℝ) ≤ c d * ((n : ℝ) / d) := mul_le_mul_of_nonneg_left this (hc d)
      _ = (n : ℝ) * (c d / d) := by ring
  have hmass : ∑ d ∈ Ioc 0 n, c d / d + ∑ d ∈ Ioc n X, c d / d ≤ m := by
    rw [sum_Ioc_consecutive _ (Nat.zero_le n) hnX]
    exact sum_le_hasSum _ (fun d _ => div_nonneg (hc d) (Nat.cast_nonneg d)) hm
  rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hmass hn]

private theorem criticalGeometricWeight_nonneg (p d : ℕ) : 0 ≤ criticalGeometricWeight p d := by
  unfold criticalGeometricWeight; split_ifs <;> positivity

/-- **The threshold `|a| = √p` is sharp.** The geometric weight has unbounded receiver energy while
its local-factor image `δ₁` has receiver energy identically zero. -/
theorem criticalLine_sharpness {p : ℕ} (hp : p.Prime) :
    (∀ T, weightPronicEnergy (localFactorWeight (criticalGeometricWeight p) p (Real.sqrt p))
        (1 / (1 - (Real.sqrt p)⁻¹) - Real.sqrt p * (1 / (1 - (Real.sqrt p)⁻¹) / p)) T = 0) ∧
    ¬ ∃ B, ∀ T, weightPronicEnergy (criticalGeometricWeight p) (1 / (1 - (Real.sqrt p)⁻¹)) T ≤ B := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast hp.one_lt)
  have hm := hasSum_criticalGeometricWeight_div hp
  set s := Real.sqrt (p : ℝ) with hs
  have hs0 : 0 < s := by linarith
  have hsq : s * s = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
  set m := 1 / (1 - s⁻¹) with hmdef
  constructor
  · have hmean : m - s * (m / p) = 1 := by
      have h3 : s - 1 ≠ 0 := by linarith
      have hm' : m = s / (s - 1) := by
        rw [hmdef, show (1 : ℝ) - s⁻¹ = (s - 1) / s by field_simp, one_div_div]
      rw [hm', ← hsq]
      field_simp
    intro T
    rw [hmean]
    unfold weightPronicEnergy
    refine sum_eq_zero fun n _ => ?_
    have hloc := localFactorWeight_criticalGeometricWeight hp
    rw [← hs] at hloc
    have hA : weightCenteredPrefix (localFactorWeight (criticalGeometricWeight p) p s) 1 n = 0 := by
      rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor]
      simp_rw [hloc, ite_mul, one_mul, zero_mul]
      rw [sum_ite_eq']
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [if_pos (mem_Icc.mpr ⟨le_refl 1, hn⟩)]; simp
    rw [hA]; simp
  · rintro ⟨B, hB⟩
    set e : ℕ → ℝ := fun n => weightCenteredPrefix (criticalGeometricWeight p) m n ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))
    have he0 : ∀ n, 0 ≤ e n := fun n => by positivity
    -- the window `(n, pn]` holds the power `p^{K+1}`, so `A(n) ≤ -n/√(pn)`
    have hcell : ∀ n : ℕ, 1 ≤ n → 1 / (2 * p * (n : ℝ)) ≤ e n := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      set K := Nat.log p n
      have hK1 : p ^ K ≤ n := Nat.pow_log_le_self p (by omega)
      have hK2 : n < p ^ (K + 1) := Nat.lt_pow_succ_log_self hp.one_lt n
      have hK3 : p ^ (K + 1) ≤ p * n := by
        rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left p hK1
      have hdrift := weightCenteredPrefix_le_neg_window_drift (criticalGeometricWeight_nonneg p) hm
        (show n ≤ p * n from Nat.le_mul_of_pos_left n hp.pos)
      have hterm : criticalGeometricWeight p (p ^ (K + 1)) / ((p ^ (K + 1) : ℕ) : ℝ) ≤
          ∑ d ∈ Ioc n (p * n), criticalGeometricWeight p d / d :=
        single_le_sum (fun d _ => div_nonneg (criticalGeometricWeight_nonneg p d) (Nat.cast_nonneg d))
          (mem_Ioc.mpr ⟨hK2, hK3⟩)
      have hpow0 : 0 < s ^ (K + 1) := pow_pos hs0 _
      have hval : criticalGeometricWeight p (p ^ (K + 1)) / ((p ^ (K + 1) : ℕ) : ℝ) =
          (s ^ (K + 1))⁻¹ := by
        rw [criticalGeometricWeight_pow hp, ← hs, Nat.cast_pow, ← hsq, mul_pow]
        field_simp
      have hpn : (0 : ℝ) < p * n := by positivity
      have hroot : s ^ (K + 1) ≤ Real.sqrt (p * n) := by
        refine Real.le_sqrt_of_sq_le ?_
        rw [← pow_mul, mul_comm, pow_mul, show s ^ 2 = p by rw [sq, hsq]]
        exact_mod_cast hK3
      have hinv : (Real.sqrt (p * n))⁻¹ ≤ (s ^ (K + 1))⁻¹ := inv_anti₀ hpow0 hroot
      have hlow : (n : ℝ) * (Real.sqrt (p * n))⁻¹ ≤
          -weightCenteredPrefix (criticalGeometricWeight p) m n := by
        have := mul_le_mul_of_nonneg_left (hinv.trans (hval ▸ hterm)) hn0.le
        linarith
      have h0 : 0 ≤ (n : ℝ) * (Real.sqrt (p * n))⁻¹ := by positivity
      have hsq2 : ((n : ℝ) * (Real.sqrt (p * n))⁻¹) ^ 2 = n / p := by
        rw [mul_pow, inv_pow, Real.sq_sqrt hpn.le]
        field_simp
      have hA2 : (n : ℝ) / p ≤ weightCenteredPrefix (criticalGeometricWeight p) m n ^ 2 := by
        rw [← hsq2]; nlinarith
      simp only [e]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (n : ℝ) + 1 ≤ 2 * n := by linarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
      have hpos : 0 ≤ (n : ℝ) / p := by positivity
      calc 1 * ((n : ℝ) * ((n : ℝ) + 1)) ≤ (n : ℝ) * (2 * n) := by nlinarith
        _ = (n : ℝ) / p * (2 * p * n) := by field_simp
        _ ≤ weightCenteredPrefix (criticalGeometricWeight p) m n ^ 2 * (2 * p * n) :=
            mul_le_mul_of_nonneg_right hA2 (by positivity)
    -- bounded energy would make `Σ 1/n` converge
    have hrange : ∀ N, ∑ n ∈ range N, e n ≤ B := fun N => by
      calc ∑ n ∈ range N, e n ≤ ∑ n ∈ insert 0 (Icc 1 N), e n :=
            sum_le_sum_of_subset_of_nonneg (fun n hn => by
              rw [mem_insert, mem_Icc]; rw [mem_range] at hn; omega) fun n _ _ => he0 n
        _ = ∑ n ∈ Icc 1 N, e n := by rw [sum_insert (by simp)]; simp [e]
        _ ≤ B := hB N
    have hs : Summable e := summable_of_sum_range_le he0 hrange
    have hg : Summable (fun n : ℕ => 1 / (2 * p * ((n + 1 : ℕ) : ℝ))) :=
      ((summable_nat_add_iff 1).mpr hs).of_nonneg_of_le (fun n => by positivity)
        fun n => hcell (n + 1) (by omega)
    have h1 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) :=
      (hg.mul_left (2 * (p : ℝ))).congr fun n => by
        have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have := hp0.ne'
        field_simp
    exact Real.not_summable_one_div_natCast
      ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp h1)

/-! ### Parity flips at one prime -/

/-- The parity flip at a prime `p`: `c^{(p)}(d) = (-1)^{v_p(d)} c(d)`. -/
def primeParityFlip (c : ℕ → ℝ) (p : ℕ) (d : ℕ) : ℝ := (-1 : ℝ) ^ d.factorization p * c d

/-- For a weight multiplicative along `p` (`c(pd) = x c(d)`), the flip satisfies
`c^{(p)} ⋆ (δ₁ + x δ_p) = c ⋆ (δ₁ - x δ_p)`. -/
theorem localFactorWeight_primeParityFlip {c : ℕ → ℝ} {p : ℕ} (hp : p.Prime) {x : ℝ}
    (hc : ∀ d, c (p * d) = x * c d) (hc0 : c 0 = 0) :
    localFactorWeight (primeParityFlip c p) p (-x) = localFactorWeight c p x := by
  funext d
  unfold localFactorWeight primeParityFlip
  by_cases hd : p ∣ d
  · obtain ⟨e, rfl⟩ := hd
    rw [if_pos (dvd_mul_right p e), if_pos (dvd_mul_right p e), Nat.mul_div_cancel_left e hp.pos]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp [hc0]
    · rw [Nat.factorization_mul hp.ne_zero he.ne', Finsupp.add_apply,
        Nat.Prime.factorization_self hp, hc e]
      ring
  · rw [if_neg hd, if_neg hd, Nat.factorization_eq_zero_of_not_dvd hd, pow_zero, one_mul]
    ring

/-- **One parity flip never separates.** For a weight multiplicative along `p` with `|x| < √p`,
the receiver energy of `c` (mean `m`) is bounded iff that of its parity flip (mean `m'`) is. -/
theorem bounded_weightPronicEnergy_primeParityFlip_iff {c : ℕ → ℝ} {p : ℕ} (hp : p.Prime) {x : ℝ}
    (hc : ∀ d, c (p * d) = x * c d) (hc0 : c 0 = 0) (hx : |x| < Real.sqrt p) {m m' : ℝ}
    (hm : HasSum (fun d : ℕ => c d / d) m)
    (hm' : HasSum (fun d : ℕ => primeParityFlip c p d / d) m') :
    (∃ B, ∀ T, weightPronicEnergy c m T ≤ B) ↔
      (∃ B, ∀ T, weightPronicEnergy (primeParityFlip c p) m' T ≤ B) := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hfun := localFactorWeight_primeParityFlip hp hc hc0
  -- both local-factor images are the same weight, so they have the same mean
  have h1 := hasSum_localFactorWeight_div hm hp1 x
  have h2 := hasSum_localFactorWeight_div hm' hp1 (-x)
  rw [hfun] at h2
  have hmeq : m' - -x * (m' / p) = m - x * (m / p) := h2.unique h1
  rw [bounded_weightPronicEnergy_localFactor_iff c m hp1 hx,
    bounded_weightPronicEnergy_localFactor_iff (primeParityFlip c p) m' hp1
      (by rwa [abs_neg] : |-x| < Real.sqrt p), hfun, hmeq]

/-- The `χ₄` weight is multiplicative along every prime: `c_χ(pd) = χ₄(p) p^{-ε} c_χ(d)`. -/
theorem dampedSignWeight_chiFour_mul_prime (ε : ℝ) (p d : ℕ) :
    dampedSignWeight chiFour ε (p * d) = (chiFour p * (p : ℝ) ^ (-ε)) * dampedSignWeight chiFour ε d := by
  unfold dampedSignWeight
  rw [chiFour_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg d)]
  ring

/-- **Flipping the parity of the `χ₄` weight at any single prime preserves its growth class.** -/
theorem bounded_weightPronicEnergy_chiFour_flip_iff {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime)
    {m' : ℝ} (hm' : HasSum (fun d : ℕ =>
      primeParityFlip (dampedSignWeight chiFour ε) p d / d) m') :
    (∃ B, ∀ T, weightPronicEnergy (dampedSignWeight chiFour ε) (chiFourDampedMass ε) T ≤ B) ↔
      (∃ B, ∀ T, weightPronicEnergy (primeParityFlip (dampedSignWeight chiFour ε) p) m' T ≤ B) := by
  have hm : HasSum (fun d : ℕ => dampedSignWeight chiFour ε d / d) (chiFourDampedMass ε) :=
    (summable_dampedSignWeight_div (by norm_num : (0 : ℝ) ≤ 1) hε abs_sum_range_chiFour_le).hasSum
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hx : |chiFour p * (p : ℝ) ^ (-ε)| < Real.sqrt p := by
    have hχ : |chiFour p| ≤ 1 := by rw [chiFour_eq]; split_ifs <;> norm_num
    have hpow : (p : ℝ) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_lt.le) (by linarith)
    have hs1 : (1 : ℝ) < Real.sqrt p := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast hp.one_lt)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hp0.le _)]
    calc |chiFour p| * (p : ℝ) ^ (-ε) ≤ 1 * 1 :=
          mul_le_mul hχ hpow (Real.rpow_nonneg hp0.le _) (by norm_num)
      _ < Real.sqrt p := by linarith
  exact bounded_weightPronicEnergy_primeParityFlip_iff hp (dampedSignWeight_chiFour_mul_prime ε p)
    (by simp [dampedSignWeight, chiFour_eq, Real.zero_rpow (show -ε ≠ 0 by linarith)]) hx hm hm'

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
