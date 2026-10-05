import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitiveLaplace
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitiveCumulant
import GaloisForLFunctions.RHTower.XiLocalZeroDensity
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import GaloisForLFunctions.RHTower.XiDivisorDiagonalTraceClass

/-!
# Single-damping source derivatives of the reciprocal Xi logarithm

With `α_q` the spectral points (every multiplicity copy), `w_q = α_q⁻¹`, `Φ(x) = ξ(1/2+x)/ξ(1/2)`,
`H(p) = log Φ(1/p)` and the cancelled atoms `C_n(z, w) = 2z^{-n} - (z - iw)^{-n} - (z + iw)^{-n}`:

* (S5) `z^n (z²+w²)^n C_n(z,w) = 2 Σ_{k=1}^n [C(n,k) - (-1)^k C(n,2k)] z^{2n-2k} w^{2k}`;
* `C_n(z,w) = 2w² Σ_{j<n} z^{-(j+1)} Σ_{i<n-j} (z+iw)^{-(i+1)} (z-iw)^{-(n-j-i)}`, hence
  `|C_n(z,w)| ≤ 2n²|w|²/m^{n+2}` whenever `m ≤ |z|, |z - iw|, |z + iw|`;
* (S6) `|p ± iw|² = p² + (1 ± 2p Im α)/|α|²`;
* for real `p > 0`: `p ± iw_q ≠ 0` with a uniform positive lower bound over all copies;
* (S4) `H'(p) = -(1/2) Σ_q Re C_1(p, w_q)` for every `p > 0`, from the partial-fraction expansion of
  `ξ'/ξ` and the reflection `α ↦ -α` of the copies;
* (S1) for every `p > 0` and `n ≥ 1`, `T_n(p) := (-1)^n H^{(n)}(p)/(n-1)! = (1/2) Σ_q Re C_n(p, w_q)`,
  absolutely, by locally uniform convergence of the holomorphic extension
  `𝓗(z) = -(1/2) Σ_q C_1(z, w_q)` and Weierstrass differentiation.
-/

open Complex Filter Topology Set

noncomputable section

namespace RHTower

local notation "Φ" => liClockThetaGeneratorReal

/-- The cancelled atom `C_n(z, w) = 2z^{-n} - (z - iw)^{-n} - (z + iw)^{-n}`. -/
def liClockStripAtom (n : ℕ) (z w : ℂ) : ℂ :=
  2 * (z ^ n)⁻¹ - ((z - I * w) ^ n)⁻¹ - ((z + I * w) ^ n)⁻¹

/-- The single-damping coefficient `T_n(p) = (-1)^n H^{(n)}(p)/(n-1)!`, `H(p) = log Φ(1/p)`. -/
def liClockStripCoefficient (n : ℕ) (p : ℝ) : ℝ :=
  (-1) ^ n * iteratedDeriv n (fun q : ℝ => Real.log (Φ q⁻¹)) p / ((n - 1).factorial : ℝ)

local notation "C" => liClockStripAtom
local notation "w" => fun q : XiZeroCopy => (xiSpectralPoint q)⁻¹

/-! ## Exact algebra of the cancelled atoms -/

/-- `x^{-n} - y^{-n} = (y - x) Σ_{j<n} x^{-(j+1)} y^{-(n-j)}`. -/
theorem inv_pow_sub_inv_pow_eq_sum {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) :
    (x ^ n)⁻¹ - (y ^ n)⁻¹ =
      (y - x) * ∑ j ∈ Finset.range n, (x ^ (j + 1))⁻¹ * (y ^ (n - j))⁻¹ := by
  have h := Finset.sum_range_sub (fun j => (x ^ j)⁻¹ * (y ^ (n - j))⁻¹) n
  simp only [Nat.sub_self, pow_zero, inv_one, mul_one, Nat.sub_zero, one_mul] at h
  rw [← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j < n := Finset.mem_range.1 hj
  obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
  have hk' : n - (j + 1) = k := by omega
  rw [hk, hk']
  field_simp
  ring

/-- **Double-sum form of the cancelled atom.** -/
theorem liClockStripAtom_eq_double_sum (n : ℕ) {z v : ℂ} (hz : z ≠ 0) (ha : z - I * v ≠ 0)
    (hb : z + I * v ≠ 0) :
    C n z v = 2 * v ^ 2 * ∑ j ∈ Finset.range n, (z ^ (j + 1))⁻¹ *
      ∑ i ∈ Finset.range (n - j), ((z + I * v) ^ (i + 1))⁻¹ * ((z - I * v) ^ (n - j - i))⁻¹ := by
  set a := z - I * v
  set b := z + I * v
  have key : C n z v = I * v * ∑ j ∈ Finset.range n,
      (z ^ (j + 1))⁻¹ * ((b ^ (n - j))⁻¹ - (a ^ (n - j))⁻¹) := by
    have hsplit : C n z v = ((z ^ n)⁻¹ - (a ^ n)⁻¹) + ((z ^ n)⁻¹ - (b ^ n)⁻¹) := by
      unfold liClockStripAtom; ring
    rw [hsplit, inv_pow_sub_inv_pow_eq_sum hz ha, inv_pow_sub_inv_pow_eq_sum hz hb,
      show a - z = -(I * v) by simp [a], show b - z = I * v by simp [b]]
    have e : ∑ j ∈ Finset.range n, (z ^ (j + 1))⁻¹ * ((b ^ (n - j))⁻¹ - (a ^ (n - j))⁻¹) =
        ∑ j ∈ Finset.range n, (z ^ (j + 1))⁻¹ * (b ^ (n - j))⁻¹ -
          ∑ j ∈ Finset.range n, (z ^ (j + 1))⁻¹ * (a ^ (n - j))⁻¹ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => mul_sub _ _ _
    rw [e]
    ring
  rw [key]
  have e2 : ∀ j ∈ Finset.range n, (z ^ (j + 1))⁻¹ * ((b ^ (n - j))⁻¹ - (a ^ (n - j))⁻¹) =
      -(2 * (I * v)) * ((z ^ (j + 1))⁻¹ *
        ∑ i ∈ Finset.range (n - j), (b ^ (i + 1))⁻¹ * (a ^ (n - j - i))⁻¹) := fun j _ => by
    rw [inv_pow_sub_inv_pow_eq_sum hb ha (n - j), show a - b = -(2 * (I * v)) by simp [a, b]; ring]
    ring
  rw [Finset.sum_congr rfl e2, ← Finset.mul_sum]
  set S := ∑ j ∈ Finset.range n, (z ^ (j + 1))⁻¹ *
    ∑ i ∈ Finset.range (n - j), (b ^ (i + 1))⁻¹ * (a ^ (n - j - i))⁻¹
  rw [show I * v * (-(2 * (I * v)) * S) = -(2 * (I * I)) * v ^ 2 * S by ring, I_mul_I]
  ring

private theorem norm_inv_pow_le {x : ℂ} {m : ℝ} (hm : 0 < m) (hx : m ≤ ‖x‖) (k : ℕ) :
    ‖(x ^ k)⁻¹‖ ≤ (m ^ k)⁻¹ := by
  rw [norm_inv, norm_pow]
  exact inv_anti₀ (pow_pos hm k) (pow_le_pow_left₀ hm.le hx k)

/-- **Second-difference bound.**  `|C_n(z,w)| ≤ 2n²|w|²/m^{n+2}` when `m ≤ |z|, |z ± iw|`. -/
theorem norm_liClockStripAtom_le (n : ℕ) {z v : ℂ} {m : ℝ} (hm : 0 < m) (hz : m ≤ ‖z‖)
    (ha : m ≤ ‖z - I * v‖) (hb : m ≤ ‖z + I * v‖) :
    ‖C n z v‖ ≤ 2 * n ^ 2 * ‖v‖ ^ 2 / m ^ (n + 2) := by
  have hz0 : z ≠ 0 := norm_pos_iff.1 (hm.trans_le hz)
  have ha0 : z - I * v ≠ 0 := norm_pos_iff.1 (hm.trans_le ha)
  have hb0 : z + I * v ≠ 0 := norm_pos_iff.1 (hm.trans_le hb)
  rw [liClockStripAtom_eq_double_sum n hz0 ha0 hb0, norm_mul, norm_mul, norm_pow,
    show ‖(2 : ℂ)‖ = 2 by simp]
  have hterm : ∀ j ∈ Finset.range n, ‖(z ^ (j + 1))⁻¹ *
      ∑ i ∈ Finset.range (n - j), ((z + I * v) ^ (i + 1))⁻¹ * ((z - I * v) ^ (n - j - i))⁻¹‖ ≤
        n * (m ^ (n + 2))⁻¹ := by
    intro j hj
    have hjn : j < n := Finset.mem_range.1 hj
    rw [norm_mul]
    have hin : ‖∑ i ∈ Finset.range (n - j), ((z + I * v) ^ (i + 1))⁻¹ *
        ((z - I * v) ^ (n - j - i))⁻¹‖ ≤ (n - j : ℕ) * (m ^ (n - j + 1))⁻¹ := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ i ∈ Finset.range (n - j), ‖((z + I * v) ^ (i + 1))⁻¹ *
          ((z - I * v) ^ (n - j - i))⁻¹‖ ≤ (m ^ (n - j + 1))⁻¹ := by
        intro i hi
        have hin : i < n - j := Finset.mem_range.1 hi
        rw [norm_mul]
        refine (mul_le_mul (norm_inv_pow_le hm hb _) (norm_inv_pow_le hm ha _) (norm_nonneg _)
          (by positivity)).trans_eq ?_
        rw [← mul_inv, ← pow_add, show i + 1 + (n - j - i) = n - j + 1 by omega]
      refine (Finset.sum_le_sum this).trans_eq ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc ‖(z ^ (j + 1))⁻¹‖ * ‖∑ i ∈ Finset.range (n - j), ((z + I * v) ^ (i + 1))⁻¹ *
          ((z - I * v) ^ (n - j - i))⁻¹‖
        ≤ (m ^ (j + 1))⁻¹ * ((n - j : ℕ) * (m ^ (n - j + 1))⁻¹) :=
          mul_le_mul (norm_inv_pow_le hm hz _) hin (norm_nonneg _) (by positivity)
      _ = (n - j : ℕ) * (m ^ (n + 2))⁻¹ := by
          rw [mul_left_comm, ← mul_inv, ← pow_add, show j + 1 + (n - j + 1) = n + 2 by omega]
      _ ≤ n * (m ^ (n + 2))⁻¹ := by
          gcongr
          exact_mod_cast Nat.sub_le n j
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  calc 2 * ‖v‖ ^ 2 * ‖∑ j ∈ Finset.range n, (z ^ (j + 1))⁻¹ *
        ∑ i ∈ Finset.range (n - j), ((z + I * v) ^ (i + 1))⁻¹ * ((z - I * v) ^ (n - j - i))⁻¹‖
      ≤ 2 * ‖v‖ ^ 2 * (n * (n * (m ^ (n + 2))⁻¹)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * n ^ 2 * ‖v‖ ^ 2 / m ^ (n + 2) := by
        field_simp

/-- **Numerator identity (S5).**
`z^n (z²+w²)^n C_n(z,w) = 2 Σ_{k=1}^n [C(n,k) - (-1)^k C(n,2k)] z^{2n-2k} w^{2k}`. -/
theorem liClockStripAtom_numerator (n : ℕ) {z v : ℂ} (hz : z ≠ 0) (ha : z - I * v ≠ 0)
    (hb : z + I * v ≠ 0) :
    z ^ n * (z ^ 2 + v ^ 2) ^ n * C n z v =
      2 * ∑ k ∈ Finset.Icc 1 n, ((n.choose k : ℂ) - (-1) ^ k * (n.choose (2 * k) : ℂ)) *
        z ^ (2 * n - 2 * k) * v ^ (2 * k) := by
  have hab : (z - I * v) * (z + I * v) = z ^ 2 + v ^ 2 := by
    rw [show (z - I * v) * (z + I * v) = z ^ 2 - (I * I) * v ^ 2 by ring, I_mul_I]; ring
  -- the full numerator
  have hnum : z ^ n * (z ^ 2 + v ^ 2) ^ n * C n z v =
      2 * (z ^ 2 + v ^ 2) ^ n - z ^ n * ((z + I * v) ^ n + (z - I * v) ^ n) := by
    unfold liClockStripAtom
    rw [← hab, mul_pow]
    field_simp
    ring
  rw [hnum]
  -- binomial expansions
  have hA : (z ^ 2 + v ^ 2) ^ n = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℂ) * z ^ (2 * n - 2 * k) * v ^ (2 * k) := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [← pow_mul, ← pow_mul, show 2 * (n - k) = 2 * n - 2 * k by omega]
    ring
  have hB : (z + I * v) ^ n + (z - I * v) ^ n = ∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℂ) * z ^ (n - j) * ((I * v) ^ j + (-(I * v)) ^ j) := by
    rw [add_comm z (I * v), add_pow, sub_eq_add_neg, add_comm z (-(I * v)), add_pow,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- only even indices survive
  have hB' : (z + I * v) ^ n + (z - I * v) ^ n = ∑ k ∈ Finset.range (n + 1),
      2 * (-1) ^ k * (n.choose (2 * k) : ℂ) * z ^ (n - 2 * k) * v ^ (2 * k) := by
    rw [hB]
    have hext : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) * z ^ (n - j) *
        ((I * v) ^ j + (-(I * v)) ^ j) = ∑ j ∈ Finset.range (2 * (n + 1)),
        (n.choose j : ℂ) * z ^ (n - j) * ((I * v) ^ j + (-(I * v)) ^ j) := by
      have : ∑ j ∈ Finset.range (n + 1), (n.choose (n + 1 + j) : ℂ) * z ^ (n - (n + 1 + j)) *
          ((I * v) ^ (n + 1 + j) + (-(I * v)) ^ (n + 1 + j)) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      rw [show 2 * (n + 1) = (n + 1) + (n + 1) by ring,
        Finset.sum_range_add (fun j => (n.choose j : ℂ) * z ^ (n - j) *
          ((I * v) ^ j + (-(I * v)) ^ j)) (n + 1) (n + 1), this, add_zero]
    have hpair : ∀ m : ℕ, ∑ j ∈ Finset.range (2 * m), (n.choose j : ℂ) * z ^ (n - j) *
        ((I * v) ^ j + (-(I * v)) ^ j) = ∑ k ∈ Finset.range m,
        2 * (-1) ^ k * (n.choose (2 * k) : ℂ) * z ^ (n - 2 * k) * v ^ (2 * k) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
          ih, Finset.sum_range_succ]
        have hodd : (I * v) ^ (2 * m + 1) + (-(I * v)) ^ (2 * m + 1) = 0 := by
          rw [Odd.neg_pow ⟨m, rfl⟩]; ring
        have heven : (I * v) ^ (2 * m) + (-(I * v)) ^ (2 * m) =
            2 * (-1) ^ m * v ^ (2 * m) := by
          rw [Even.neg_pow ⟨m, by ring⟩, pow_mul, mul_pow, I_sq, pow_mul]
          ring
        rw [hodd, heven]
        ring
    rw [hext, hpair]
  have hC : z ^ n * ∑ k ∈ Finset.range (n + 1),
      2 * (-1) ^ k * (n.choose (2 * k) : ℂ) * z ^ (n - 2 * k) * v ^ (2 * k) =
      ∑ k ∈ Finset.range (n + 1),
        2 * (-1) ^ k * (n.choose (2 * k) : ℂ) * z ^ (2 * n - 2 * k) * v ^ (2 * k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : 2 * k ≤ n
    · rw [show 2 * n - 2 * k = n + (n - 2 * k) by omega, pow_add]; ring
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [hA, hB', hC, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  have h0 : 2 * ((n.choose 0 : ℂ) * z ^ (2 * n - 2 * 0) * v ^ (2 * 0)) -
      2 * (-1) ^ 0 * (n.choose (2 * 0) : ℂ) * z ^ (2 * n - 2 * 0) * v ^ (2 * 0) = 0 := by
    simp
  rw [h0, add_zero, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [add_comm 1 k]
  ring

/-! ## The damping shifts `p ± iw_q` -/

/-- **(S6)** `|p ± iα⁻¹|² = p² + (1 ± 2p Im α)/|α|²`. -/
theorem normSq_ofReal_add_I_mul_inv (p : ℝ) {α : ℂ} (hα : α ≠ 0) :
    normSq ((p : ℂ) + I * α⁻¹) = p ^ 2 + (1 + 2 * p * α.im) / normSq α ∧
      normSq ((p : ℂ) - I * α⁻¹) = p ^ 2 + (1 - 2 * p * α.im) / normSq α := by
  have hN : α.re ^ 2 + α.im ^ 2 ≠ 0 := by
    rw [sq, sq, ← normSq_apply]; exact (normSq_pos.2 hα).ne'
  constructor <;>
  · simp only [normSq_apply, add_re, sub_re, add_im, sub_im, ofReal_re, ofReal_im, mul_re, mul_im,
      I_re, I_im, inv_re, inv_im]
    field_simp
    ring

/-- For real `p > 0` the damping shifts `p ± iw_q` never vanish: otherwise `ξ` would vanish at
the real point `1/2 ± 1/p`. -/
theorem ofReal_add_I_mul_inv_xiSpectralPoint_ne_zero {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    (p : ℂ) + I * (xiSpectralPoint q)⁻¹ ≠ 0 ∧ (p : ℂ) - I * (xiSpectralPoint q)⁻¹ ≠ 0 := by
  have hz := XiC_xiSpectralPoint_eq_zero q
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  constructor
  · intro h
    have hw : (xiSpectralPoint q)⁻¹ = I * p := by
      linear_combination (-I) * h + (xiSpectralPoint q)⁻¹ * I_sq
    have hα : xiSpectralPoint q = (I * p)⁻¹ := by rw [← hw, inv_inv]
    rw [hα, XiC] at hz
    have e : (1 / 2 : ℂ) + (I * p)⁻¹ * I = 1 / 2 + ((p⁻¹ : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [e] at hz
    exact xi_ofReal_shift_ne_zero p⁻¹ hz
  · intro h
    have hw : (xiSpectralPoint q)⁻¹ = -(I * p) := by
      linear_combination I * h + (xiSpectralPoint q)⁻¹ * I_sq
    have hα : xiSpectralPoint q = (-(I * p))⁻¹ := by rw [← hw, inv_inv]
    rw [hα, XiC] at hz
    have e : (1 / 2 : ℂ) + (-(I * p))⁻¹ * I = 1 / 2 + ((-p⁻¹ : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [e] at hz
    exact xi_ofReal_shift_ne_zero (-p⁻¹) hz

private theorem exists_pos_le_of_tendsto_cofinite {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 < f i)
    {L : ℝ} (hL : 0 < L) (hlim : Tendsto f cofinite (𝓝 L)) : ∃ δ, 0 < δ ∧ ∀ i, δ ≤ f i := by
  classical
  have hfin : {i | f i ≤ L / 2}.Finite := by
    have h := hlim.eventually (lt_mem_nhds (half_lt_self hL))
    rw [Filter.eventually_cofinite] at h
    simpa [not_lt] using h
  by_cases hne : hfin.toFinset.Nonempty
  · obtain ⟨i₀, -, hmin⟩ := hfin.toFinset.exists_min_image f hne
    refine ⟨min (L / 2) (f i₀), lt_min (half_pos hL) (hf i₀), fun i => ?_⟩
    by_cases hi : f i ≤ L / 2
    · exact (min_le_right _ _).trans (hmin i (by simpa using hi))
    · exact (min_le_left _ _).trans (le_of_lt (not_le.1 hi))
  · refine ⟨L / 2, half_pos hL, fun i => ?_⟩
    by_contra h
    exact hne ⟨i, by simpa using (not_le.1 h).le⟩

/-- The reciprocal spectral points tend to `0` along the cofinite filter. -/
theorem tendsto_inv_xiSpectralPoint_cofinite :
    Tendsto (fun q => (xiSpectralPoint q)⁻¹) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (summable_norm_inv_xiSpectralPoint_sq.tendsto_cofinite_zero).sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using h

/-- **Uniform gap.**  For `p > 0` there is `0 < δ ≤ p` with `δ ≤ |p ± iw_q|` for every copy. -/
theorem exists_liClockStrip_gap {p : ℝ} (hp : 0 < p) :
    ∃ δ, 0 < δ ∧ δ ≤ p ∧ ∀ q, δ ≤ ‖(p : ℂ) - I * (xiSpectralPoint q)⁻¹‖ ∧
      δ ≤ ‖(p : ℂ) + I * (xiSpectralPoint q)⁻¹‖ := by
  set f := fun q : XiZeroCopy =>
    min ‖(p : ℂ) - I * (xiSpectralPoint q)⁻¹‖ ‖(p : ℂ) + I * (xiSpectralPoint q)⁻¹‖
  have hf : ∀ q, 0 < f q := fun q =>
    lt_min (norm_pos_iff.2 (ofReal_add_I_mul_inv_xiSpectralPoint_ne_zero hp q).2)
      (norm_pos_iff.2 (ofReal_add_I_mul_inv_xiSpectralPoint_ne_zero hp q).1)
  have hlim : Tendsto f cofinite (𝓝 p) := by
    have h := tendsto_inv_xiSpectralPoint_cofinite
    have h1 := ((tendsto_const_nhds (x := (p : ℂ))).sub
      ((tendsto_const_nhds (x := I)).mul h)).norm
    have h2 := ((tendsto_const_nhds (x := (p : ℂ))).add
      ((tendsto_const_nhds (x := I)).mul h)).norm
    simpa [abs_of_pos hp] using h1.min h2
  obtain ⟨δ, hδ, hle⟩ := exists_pos_le_of_tendsto_cofinite hf hp hlim
  exact ⟨min δ p, lt_min hδ hp, min_le_right _ _, fun q =>
    ⟨(min_le_left _ _).trans ((hle q).trans (min_le_left _ _)),
      (min_le_left _ _).trans ((hle q).trans (min_le_right _ _))⟩⟩

/-- The real cancelled family is absolutely summable at every `p > 0` and every order. -/
theorem summable_norm_liClockStripAtom {p : ℝ} (hp : 0 < p) (n : ℕ) :
    Summable fun q => ‖C n p (w q)‖ := by
  obtain ⟨δ, hδ, hδp, hgap⟩ := exists_liClockStrip_gap hp
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => norm_liClockStripAtom_le n hδ
    (by simpa [abs_of_pos hp] using hδp) (hgap q).1 (hgap q).2)
    ((summable_norm_inv_xiSpectralPoint_sq.mul_left (2 * (n : ℝ) ^ 2)).div_const (δ ^ (n + 2)) |>.congr
      fun q => by ring)

/-! ## The first source derivative -/

private theorem partialFraction_term_eq {p : ℝ} (hp : 0 < p) (q : XiZeroCopy) :
    -((p : ℂ) ^ 2)⁻¹ * (((q.1 : ℂ) - 1 / 2)⁻¹ + (1 / 2 + ((p⁻¹ : ℝ) : ℂ) - (q.1 : ℂ))⁻¹) =
      -((xiSpectralPoint q)⁻¹) ^ 2 / ((p : ℂ) ^ 2 * ((p : ℂ) + I * (xiSpectralPoint q)⁻¹)) := by
  set α := xiSpectralPoint q with hαdef
  have hα : α ≠ 0 := xiSpectralPoint_ne_zero q
  have hρ : (q.1 : ℂ) - 1 / 2 = I * α := by
    rw [hαdef, xiSpectralPoint_eq_support, xiSpectralPointSupport]
    rw [show I * (((q.1 : ℂ) - 1 / 2) * -I) = -(I * I) * ((q.1 : ℂ) - 1 / 2) by ring, I_mul_I]
    ring
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hsh := (ofReal_add_I_mul_inv_xiSpectralPoint_ne_zero hp q).1
  rw [← hαdef] at hsh
  have hs : (1 / 2 + ((p⁻¹ : ℝ) : ℂ) - (q.1 : ℂ)) = ((p : ℂ) + I * α⁻¹) * (-I * α / p) := by
    rw [show (1 / 2 + ((p⁻¹ : ℝ) : ℂ) - (q.1 : ℂ)) = (p : ℂ)⁻¹ - ((q.1 : ℂ) - 1 / 2) by
      push_cast; ring, hρ]
    field_simp
    linear_combination I_sq
  have hIα : I * α ≠ 0 := mul_ne_zero I_ne_zero hα
  have hpaI : (p : ℂ) * α + I ≠ 0 := by
    intro h0
    apply hsh
    rw [show (p : ℂ) + I * α⁻¹ = ((p : ℂ) * α + I) / α by field_simp, h0, zero_div]
  rw [hρ, hs]
  field_simp
  ring

private theorem half_reflect_identity {p v : ℂ} (hp : p ≠ 0) (ha : p - I * v ≠ 0)
    (hb : p + I * v ≠ 0) :
    (-v ^ 2 / (p ^ 2 * (p + I * v)) + -(-v) ^ 2 / (p ^ 2 * (p + I * -v))) / 2 =
      -(1 / 2) * C 1 p v := by
  have hab : (p - I * v) * (p + I * v) = p ^ 2 + v ^ 2 := by linear_combination (-v ^ 2) * I_sq
  have hne : p ^ 2 + v ^ 2 ≠ 0 := by rw [← hab]; exact mul_ne_zero ha hb
  have hS : (p - I * v)⁻¹ + (p + I * v)⁻¹ = 2 * p / (p ^ 2 + v ^ 2) := by
    rw [← hab]; field_simp; ring
  rw [show p + I * -v = p - I * v by ring]
  unfold liClockStripAtom
  simp only [pow_one]
  have e1 : (-v ^ 2 / (p ^ 2 * (p + I * v)) + -(-v) ^ 2 / (p ^ 2 * (p - I * v))) / 2 =
      -(v ^ 2 / (2 * p ^ 2)) * ((p - I * v)⁻¹ + (p + I * v)⁻¹) := by
    field_simp
    ring
  have e2 : -(1 / 2) * (2 * p⁻¹ - (p - I * v)⁻¹ - (p + I * v)⁻¹) =
      -(1 / 2) * (2 * p⁻¹ - ((p - I * v)⁻¹ + (p + I * v)⁻¹)) := by ring
  rw [e1, e2, hS]
  field_simp
  ring

/-- **(S4)** `H'(p) = -(1/2) Σ_q Re C_1(p, w_q)` for every `p > 0`. -/
theorem hasDerivAt_log_liClockThetaGeneratorReal_inv_eq_tsum {p : ℝ} (hp : 0 < p) :
    HasDerivAt (fun q : ℝ => Real.log (Φ q⁻¹)) (-(1 / 2) * ∑' q, (C 1 p (w q)).re) p := by
  have hd := (hasDerivAt_liClockThetaLogGenerator p⁻¹).comp p (hasDerivAt_inv hp.ne')
  refine hd.congr_deriv ?_
  rw [liClockThetaGeneratorRealDeriv_div_eq_xiRealLogDeriv]
  unfold xiRealLogDeriv
  have hxi : xi (1 / 2 + ((p⁻¹ : ℝ) : ℂ)) ≠ 0 := xi_ofReal_shift_ne_zero p⁻¹
  rw [logDeriv_xi_eq_partialFraction hxi]
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  set G : XiZeroCopy → ℂ := fun q =>
    -((xiSpectralPoint q)⁻¹) ^ 2 / ((p : ℂ) ^ 2 * ((p : ℂ) + I * (xiSpectralPoint q)⁻¹))
  have hsumPF := summable_xiPartialFractionTerm hxi
  have hGsum : Summable G :=
    (hsumPF.mul_left (-((p : ℂ) ^ 2)⁻¹)).congr fun q => partialFraction_term_eq hp q
  have hGσ : Summable (fun q => G (xiZeroCopyReflectEquiv q)) :=
    (Equiv.summable_iff xiZeroCopyReflectEquiv).2 hGsum
  have hhalf : ∀ q, (G q + G (xiZeroCopyReflectEquiv q)) / 2 = -(1 / 2) * C 1 p (w q) := by
    intro q
    have hsh := ofReal_add_I_mul_inv_xiSpectralPoint_ne_zero hp q
    simp only [G, xiSpectralPoint_reflect, inv_neg]
    exact half_reflect_identity hp' hsh.2 hsh.1
  have htsum : ∑' q, G q = ∑' q, -(1 / 2) * C 1 p (w q) := by
    have h1 : ∑' q, G (xiZeroCopyReflectEquiv q) = ∑' q, G q := Equiv.tsum_eq _ _
    calc ∑' q, G q = (∑' q, G q + ∑' q, G (xiZeroCopyReflectEquiv q)) / 2 := by rw [h1]; ring
      _ = ∑' q, (G q + G (xiZeroCopyReflectEquiv q)) / 2 := by
          rw [← hGsum.tsum_add hGσ, tsum_div_const]
      _ = _ := tsum_congr hhalf
  have hCsum : Summable fun q => -(1 / 2) * C 1 p (w q) :=
    ((hGsum.add hGσ).div_const 2).congr hhalf
  have hval : (∑' q : XiZeroCopy,
      (((q.1 : ℂ) - 1 / 2)⁻¹ + (1 / 2 + ((p⁻¹ : ℝ) : ℂ) - (q.1 : ℂ))⁻¹)) *
      (-((p : ℂ) ^ 2)⁻¹) = ∑' q, G q := by
    rw [mul_comm, ← tsum_mul_left]
    exact tsum_congr fun q => partialFraction_term_eq hp q
  have hre : ∀ z : ℂ, z.re * (-(p ^ 2)⁻¹) = (z * (-((p : ℂ) ^ 2)⁻¹)).re := fun z => by
    rw [show (-((p : ℂ) ^ 2)⁻¹) = ((-(p ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.re_mul_ofReal]
  rw [hre, hval, htsum, Complex.re_tsum hCsum, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul]

/-- `C_1(z, w) = 2w²/(z(z² + w²))`. -/
theorem liClockStripAtom_one_eq {z v : ℂ} (hz : z ≠ 0) (ha : z - I * v ≠ 0) (hb : z + I * v ≠ 0) :
    C 1 z v = 2 * v ^ 2 / (z * (z ^ 2 + v ^ 2)) := by
  have hab : (z - I * v) * (z + I * v) = z ^ 2 + v ^ 2 := by linear_combination (-v ^ 2) * I_sq
  have hne : z ^ 2 + v ^ 2 ≠ 0 := by rw [← hab]; exact mul_ne_zero ha hb
  unfold liClockStripAtom
  rw [← hab]
  field_simp
  linear_combination (-2 * v ^ 2) * I_sq

/-- **(S4), resolvent form.**  `-H'(p) = Σ_q Re[λ_q/(p(p² + λ_q))]` with `λ_q = w_q²`. -/
theorem hasDerivAt_log_liClockThetaGeneratorReal_inv_resolvent {p : ℝ} (hp : 0 < p) :
    HasDerivAt (fun q : ℝ => Real.log (Φ q⁻¹))
      (-∑' q, ((w q) ^ 2 / ((p : ℂ) * ((p : ℂ) ^ 2 + (w q) ^ 2))).re) p := by
  refine (hasDerivAt_log_liClockThetaGeneratorReal_inv_eq_tsum hp).congr_deriv ?_
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [← tsum_mul_left, ← tsum_neg]
  refine tsum_congr fun q => ?_
  have hsh := ofReal_add_I_mul_inv_xiSpectralPoint_ne_zero hp q
  rw [liClockStripAtom_one_eq hp' hsh.2 hsh.1, mul_div_assoc,
    show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, re_ofReal_mul]
  ring

/-! ## The holomorphic extension and every source derivative -/

private theorem hasDerivAt_inv_pow_sub {c z : ℂ} (hz : z - c ≠ 0) (m : ℕ) :
    HasDerivAt (fun y => ((y - c) ^ m)⁻¹) (-(m : ℂ) * ((z - c) ^ (m + 1))⁻¹) z := by
  have h := (((hasDerivAt_id z).sub_const c).fun_pow m).inv (pow_ne_zero m hz)
  refine h.congr_deriv ?_
  simp only [id]
  cases m with
  | zero => simp
  | succ m =>
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

/-- `d/dz C_m(z, w) = -m C_{m+1}(z, w)`. -/
theorem hasDerivAt_liClockStripAtom (m : ℕ) {z v : ℂ} (hz : z ≠ 0) (ha : z - I * v ≠ 0)
    (hb : z + I * v ≠ 0) :
    HasDerivAt (fun y => C m y v) (-(m : ℂ) * C (m + 1) z v) z := by
  have h1 := hasDerivAt_inv_pow_sub (c := 0) (by simpa using hz) m
  have h2 := hasDerivAt_inv_pow_sub (c := I * v) ha m
  have h3 := hasDerivAt_inv_pow_sub (c := -(I * v)) (by simpa [sub_neg_eq_add] using hb) m
  have h := ((h1.const_mul 2).sub h2).sub h3
  have e : (fun y => C m y v) = fun y =>
      2 * ((y - 0) ^ m)⁻¹ - ((y - I * v) ^ m)⁻¹ - ((y - -(I * v)) ^ m)⁻¹ := by
    funext y; simp [liClockStripAtom, sub_neg_eq_add]
  rw [e]
  refine h.congr_deriv ?_
  simp only [liClockStripAtom, sub_zero, sub_neg_eq_add]
  ring

/-- `E_k(z, w) = -(1/2)(-1)^k k! C_{k+1}(z, w)`, the `k`-th derivative of `-(1/2) C_1(·, w)`. -/
def liClockStripDerivAtom (k : ℕ) (z v : ℂ) : ℂ :=
  -(1 / 2) * ((-1) ^ k * (k.factorial : ℂ)) * C (k + 1) z v

local notation "E" => liClockStripDerivAtom

theorem hasDerivAt_liClockStripDerivAtom (k : ℕ) {z v : ℂ} (hz : z ≠ 0) (ha : z - I * v ≠ 0)
    (hb : z + I * v ≠ 0) :
    HasDerivAt (fun y => E k y v) (E (k + 1) z v) z := by
  have h := (hasDerivAt_liClockStripAtom (k + 1) hz ha hb).const_mul
    (-(1 / 2) * ((-1) ^ k * (k.factorial : ℂ)))
  refine h.congr_deriv ?_
  unfold liClockStripDerivAtom
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- The holomorphic extension `𝓗(z) = -(1/2) Σ_q C_1(z, w_q)` of `H'`. -/
def liClockStripHolomorphic (z : ℂ) : ℂ := ∑' q, E 0 z (w q)

local notation "𝓗" => liClockStripHolomorphic

private theorem differentiableOn_iteratedDeriv_of_open {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (k : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv k f) U := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv hU

/-- **Local Weierstrass differentiation.**  Around every `p > 0`, `𝓗` is holomorphic and every
complex derivative is the termwise sum `𝓗^{(k)}(p) = Σ_q E_k(p, w_q)`. -/
theorem liClockStripHolomorphic_local {p : ℝ} (hp : 0 < p) :
    ∃ r > 0, DifferentiableOn ℂ 𝓗 (Metric.ball (p : ℂ) r) ∧
      ∀ k, HasSum (fun q => E k p (w q)) (iteratedDeriv k 𝓗 p) := by
  obtain ⟨δ, hδ, hδp, hgap⟩ := exists_liClockStrip_gap hp
  set U := Metric.ball (p : ℂ) (δ / 2)
  have hU : IsOpen U := Metric.isOpen_ball
  have hmem : (p : ℂ) ∈ U := Metric.mem_ball_self (half_pos hδ)
  have hpn : ‖(p : ℂ)‖ = p := by simp [abs_of_pos hp]
  have hlow : ∀ z ∈ U, ∀ q, δ / 2 ≤ ‖z‖ ∧ δ / 2 ≤ ‖z - I * w q‖ ∧ δ / 2 ≤ ‖z + I * w q‖ := by
    intro z hz q
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 : ‖(p : ℂ)‖ ≤ ‖z‖ + ‖z - p‖ := by
      calc ‖(p : ℂ)‖ = ‖z - (z - p)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖z - p‖ := norm_sub_le _ _
    have h2 : ‖(p : ℂ) - I * w q‖ ≤ ‖z - I * w q‖ + ‖z - p‖ := by
      calc ‖(p : ℂ) - I * w q‖ = ‖(z - I * w q) - (z - p)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    have h3 : ‖(p : ℂ) + I * w q‖ ≤ ‖z + I * w q‖ + ‖z - p‖ := by
      calc ‖(p : ℂ) + I * w q‖ = ‖(z + I * w q) - (z - p)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    exact ⟨by linarith, by linarith [(hgap q).1], by linarith [(hgap q).2]⟩
  have hne : ∀ z ∈ U, ∀ q, z ≠ 0 ∧ z - I * w q ≠ 0 ∧ z + I * w q ≠ 0 := fun z hz q =>
    ⟨norm_pos_iff.1 ((half_pos hδ).trans_le (hlow z hz q).1),
      norm_pos_iff.1 ((half_pos hδ).trans_le (hlow z hz q).2.1),
      norm_pos_iff.1 ((half_pos hδ).trans_le (hlow z hz q).2.2)⟩
  have hbound : ∀ q, ∀ z ∈ U, ‖E 0 z (w q)‖ ≤ ‖w q‖ ^ 2 / (δ / 2) ^ 3 := by
    intro q z hz
    obtain ⟨h1, h2, h3⟩ := hlow z hz q
    have h := norm_liClockStripAtom_le 1 (half_pos hδ) h1 h2 h3
    have hE : ‖E 0 z (w q)‖ = ‖C 1 z (w q)‖ / 2 := by
      unfold liClockStripDerivAtom
      simp
      ring
    rw [hE]
    calc ‖C 1 z (w q)‖ / 2 ≤ (2 * ((1 : ℕ) : ℝ) ^ 2 * ‖w q‖ ^ 2 / (δ / 2) ^ (1 + 2)) / 2 := by
          gcongr
      _ = ‖w q‖ ^ 2 / (δ / 2) ^ 3 := by push_cast; ring
  have hsum : Summable fun q => ‖w q‖ ^ 2 / (δ / 2) ^ 3 :=
    summable_norm_inv_xiSpectralPoint_sq.div_const _
  have hsumAt : ∀ k (S : Finset XiZeroCopy), ∀ z ∈ U,
      HasDerivAt (fun y => ∑ q ∈ S, E k y (w q)) (∑ q ∈ S, E (k + 1) z (w q)) z :=
    fun k S z hz => HasDerivAt.fun_sum fun q _ =>
      hasDerivAt_liClockStripDerivAtom k (hne z hz q).1 (hne z hz q).2.1 (hne z hz q).2.2
  have hdiffS : ∀ k (S : Finset XiZeroCopy),
      DifferentiableOn ℂ (fun z => ∑ q ∈ S, E k z (w q)) U :=
    fun k S z hz => (hsumAt k S z hz).differentiableAt.differentiableWithinAt
  have h0 : TendstoLocallyUniformlyOn (fun S z => ∑ q ∈ S, E 0 z (w q)) 𝓗 atTop U :=
    (tendstoUniformlyOn_tsum hsum hbound).tendstoLocallyUniformlyOn
  have hk : ∀ k, TendstoLocallyUniformlyOn (fun S z => ∑ q ∈ S, E k z (w q))
      (iteratedDeriv k 𝓗) atTop U := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      have h := ih.deriv (Eventually.of_forall fun S => hdiffS k S) hU
      rw [iteratedDeriv_succ]
      refine h.congr fun S z hz => ?_
      simp only [Function.comp_apply]
      exact (hsumAt k S z hz).deriv
  exact ⟨δ / 2, half_pos hδ, h0.differentiableOn (Eventually.of_forall fun S => hdiffS 0 S) hU,
    fun k => (hk k).tendsto_at hmem⟩

/-- Real and complex derivatives of the extension agree on the positive axis. -/
theorem iteratedDeriv_re_liClockStripHolomorphic (k : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (fun y : ℝ => (𝓗 y).re) x = (iteratedDeriv k 𝓗 x).re := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv k (fun y : ℝ => (𝓗 y).re) =ᶠ[𝓝 x]
        fun y => (iteratedDeriv k 𝓗 y).re :=
      (eventually_gt_nhds hx).mono fun y hy => ih hy
    rw [heq.deriv_eq]
    obtain ⟨r, hr, hdiff, -⟩ := liClockStripHolomorphic_local hx
    have hd : DifferentiableAt ℂ (iteratedDeriv k 𝓗) (x : ℂ) :=
      (differentiableOn_iteratedDeriv_of_open hdiff Metric.isOpen_ball k).differentiableAt
        (Metric.ball_mem_nhds _ hr)
    rw [hd.hasDerivAt.real_of_complex.deriv, iteratedDeriv_succ]

private theorem re_liClockStripDerivAtom (k : ℕ) (z v : ℂ) :
    (E k z v).re = -(1 / 2) * ((-1) ^ k * (k.factorial : ℝ)) * (C (k + 1) z v).re := by
  unfold liClockStripDerivAtom
  rw [show -(1 / 2 : ℂ) * ((-1) ^ k * (k.factorial : ℂ)) =
    ((-(1 / 2) * ((-1) ^ k * (k.factorial : ℝ)) : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul]

/-- **(S1)** For every `p > 0` and `n ≥ 1`, `T_n(p) = (1/2) Σ_q Re C_n(p, w_q)`, absolutely. -/
theorem hasSum_liClockStripCoefficient {p : ℝ} (hp : 0 < p) {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun q => (C n p (w q)).re / 2) (liClockStripCoefficient n p) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨r, hr, -, hsum⟩ := liClockStripHolomorphic_local hp
  have hderiv : deriv (fun q : ℝ => Real.log (Φ q⁻¹)) =ᶠ[𝓝 p]
      fun y : ℝ => (𝓗 y).re := by
    filter_upwards [eventually_gt_nhds hp] with y hy
    rw [(hasDerivAt_log_liClockThetaGeneratorReal_inv_eq_tsum hy).deriv]
    have hs : Summable fun q => E 0 (y : ℂ) (w q) := by
      refine Summable.of_norm_bounded ((summable_norm_liClockStripAtom hy 1).mul_left (1 / 2))
        fun q => ?_
      unfold liClockStripDerivAtom
      simp
    unfold liClockStripHolomorphic
    rw [Complex.re_tsum hs, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [re_liClockStripDerivAtom]
    simp
  have hit : iteratedDeriv (m + 1) (fun q : ℝ => Real.log (Φ q⁻¹)) p =
      (iteratedDeriv m 𝓗 p).re := by
    rw [iteratedDeriv_succ', hderiv.iteratedDeriv_eq, iteratedDeriv_re_liClockStripHolomorphic m hp]
  unfold liClockStripCoefficient
  rw [hit, Nat.add_sub_cancel]
  have h := (Complex.hasSum_re (hsum m)).mul_left ((-1) ^ (m + 1) / (m.factorial : ℝ))
  have hfac : (m.factorial : ℝ) ≠ 0 := by positivity
  have e : (fun q => (C (m + 1) p (w q)).re / 2) =
      fun q => (-1) ^ (m + 1) / (m.factorial : ℝ) * (E m p (w q)).re := by
    funext q
    rw [re_liClockStripDerivAtom]
    field_simp
    ring_nf
    simp
  rw [e, show (-1) ^ (m + 1) * (iteratedDeriv m 𝓗 p).re / (m.factorial : ℝ) =
    (-1) ^ (m + 1) / (m.factorial : ℝ) * (iteratedDeriv m 𝓗 p).re by ring]
  exact h

end RHTower
