import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheOverlapThatResolvesATwistIsAnExactThreshold
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTiltedSplineHasAPolynomialConductorFloor

/-!
# The resolution threshold of a flipped prime is exact

Flip the odd powers of one prime `p`: `ω_p Λ` is `Λ` with sign `(−1)^k` on `p^k`. Its twist defect
is `2 log p · p^{-k/2}` on odd powers of `p` and `0` elsewhere, so it is summable
(`summable_abs_twistDefect_primeFlip`, `tsum_abs_twistDefect_primeFlip_le`), and its limit twist
energy is explicit (`twistLimitEnergy_primeFlip`):

`2 Σ_k d(k) k^{-1/2} M(y·y(k·)) = 4 log p Σ_{j ≥ 0} p^{-(2j+1)} M(y · y(p^{2j+1} ·))`.

Hence the overlap at which complete Weil positivity resolves `ω_p` from `0` is the exact threshold

`c_0(ω_p) = sup {c : inf_{Σβ² = 1} [Σ_m β_m² E_m(c) + 4 log p Σ_j p^{-(2j+1)} M(y·y(p^{2j+1}·))] > 0}`,

`y = Σ_m β_m e_m` (`primeFlip_resolutionThreshold_spec`): positive definite below it, negative on
an atomic test above it, for every profile without real Fourier zeros. The prime-square trial
shows that every flip is seen (`exists_primeFlip_resolutionBottom_neg`), so `c_0(ω_p) < ∞`; the
pole energy `E(c) > 0` against the bound `8 log p/√p · (1 + 2c e^c)` of the flip shows
`c_0(ω_p) → ∞` (`le_primeFlip_resolutionThreshold`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticLorentzianGeometry
  RenormalizedBiarithmeticGeometry CompletedShell ArithmeticCastelnuovoSeveri Zeta23
  ArithmeticCountingPositivity TransMetzlerWeilPositivity.BoundedOverlap
open _root_.RHTower (vonMangoldtAtom)

/-! ### The defect of a flipped prime -/

theorem twistDefect_primeFlip (p k : ℕ) :
    twistDefect (primeFlipWeight p) k = (1 - finiteFlip {p} k) * vonMangoldtAtom k :=
  vonMangoldtAtom_sub_twistCoeff_flip p k

theorem sqrt_natCast_pow (p n : ℕ) : Real.sqrt ((p : ℝ) ^ n) = Real.sqrt p ^ n := by
  rw [show ((p : ℝ) ^ n) = (Real.sqrt p ^ n) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg p)],
    Real.sqrt_sq (by positivity)]

open Classical in
/-- The prime powers of `p` carry a summable square-root mass. -/
theorem summable_primePow_inv_sqrt {p : ℕ} (hp : p.Prime) :
    Summable fun k : ℕ => if ∃ j, k = p ^ (j + 1) then 1 / Real.sqrt k else 0 := by
  have hinj : Function.Injective (fun j : ℕ => p ^ (j + 1)) := fun a b h => by
    have := Nat.pow_right_injective hp.two_le h
    simpa using this
  have hzero : Function.support (fun k : ℕ => if ∃ j, k = p ^ (j + 1) then 1 / Real.sqrt k else 0)
      ⊆ Set.range (fun j : ℕ => p ^ (j + 1)) := by
    intro k hk
    by_contra hnot
    apply hk
    show (if ∃ j, k = p ^ (j + 1) then 1 / Real.sqrt k else 0) = 0
    rw [if_neg]
    rintro ⟨j, rfl⟩
    exact hnot ⟨j, rfl⟩
  rw [← hinj.summable_iff (fun k hk => by
    by_contra hne
    exact hk (hzero hne))]
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hr : 0 ≤ 1 / Real.sqrt p := by positivity
  have hr1 : 1 / Real.sqrt p < 1 := by
    rw [div_lt_one hsp, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast hp.one_lt)
  refine ((summable_geometric_of_lt_one hr hr1).mul_left (1 / Real.sqrt p)).congr fun j => ?_
  simp only [Function.comp_apply, if_pos (⟨j, rfl⟩ : ∃ i, p ^ (j + 1) = p ^ (i + 1)),
    Nat.cast_pow, sqrt_natCast_pow]
  rw [← pow_succ', _root_.one_div_pow]

open Classical in
theorem abs_twistDefect_primeFlip_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |twistDefect (primeFlipWeight p) k| ≤
      2 * Real.log p * (if ∃ j, k = p ^ (j + 1) then 1 / Real.sqrt k else 0) := by
  rw [twistDefect_primeFlip]
  rcases flip_coeff_cases hp k with h0 | ⟨j, hkj, hc⟩
  · rw [h0, abs_zero]
    have := Real.log_natCast_nonneg p
    split_ifs <;> positivity
  · rw [if_pos ⟨j, hkj⟩]
    calc _ ≤ 2 * Real.log p / Real.sqrt k := hc
      _ = 2 * Real.log p * (1 / Real.sqrt k) := by ring

open Classical in
/-- **A flipped prime has summable defect.** -/
theorem summable_abs_twistDefect_primeFlip {p : ℕ} (hp : p.Prime) :
    Summable fun k => |twistDefect (primeFlipWeight p) k| :=
  Summable.of_nonneg_of_le (fun k => abs_nonneg _) (abs_twistDefect_primeFlip_le hp)
    ((summable_primePow_inv_sqrt hp).mul_left (2 * Real.log p))

open Classical in
/-- The total defect of a flip at `p ≥ 4` is at most `4 log p/√p`. -/
theorem tsum_abs_twistDefect_primeFlip_le {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) :
    ∑' k, |twistDefect (primeFlipWeight p) k| ≤ 4 * Real.log p / Real.sqrt p := by
  refine Real.tsum_le_of_sum_range_le (fun k => abs_nonneg _) fun K => ?_
  calc ∑ k ∈ range K, |twistDefect (primeFlipWeight p) k|
      ≤ ∑ k ∈ range K, 2 * Real.log p *
          (if ∃ j, k = p ^ (j + 1) then 1 / Real.sqrt k else 0) :=
        sum_le_sum fun k _ => abs_twistDefect_primeFlip_le hp k
    _ = 2 * Real.log p * ∑ k ∈ range K,
          (if ∃ j, k = p ^ (j + 1) then 1 / Real.sqrt k else 0) := by rw [mul_sum]
    _ ≤ 2 * Real.log p * (2 / Real.sqrt p) :=
        mul_le_mul_of_nonneg_left (sum_primePow_inv_sqrt_le hp hp4 K)
          (mul_nonneg (by norm_num) (Real.log_natCast_nonneg p))
    _ = 4 * Real.log p / Real.sqrt p := by ring

/-! ### The explicit flip energy -/

theorem finiteFlip_singleton_pow {p : ℕ} (hp : p.Prime) (n : ℕ) :
    finiteFlip {p} (p ^ n) = (-1) ^ n := by
  rw [finiteFlip, Finset.prod_singleton, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]

theorem twistDefect_primeFlip_pow {p : ℕ} (hp : p.Prime) (n : ℕ) :
    twistDefect (primeFlipWeight p) (p ^ n) / Real.sqrt ((p ^ n : ℕ) : ℝ) =
      (1 - (-1) ^ n) * Real.log p / (p : ℝ) ^ n := by
  rw [twistDefect_primeFlip, finiteFlip_singleton_pow hp]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h2 : 2 ≤ p ^ n := hp.two_le.trans (Nat.le_self_pow hn.ne' p)
  rw [vonMangoldtAtom, if_pos h2, ArithmeticFunction.vonMangoldt_apply_pow hn.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hpos : 0 < Real.sqrt ((p ^ n : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast pow_pos hp.pos n)
  have hsq : Real.sqrt ((p ^ n : ℕ) : ℝ) * Real.sqrt ((p ^ n : ℕ) : ℝ) = (p : ℝ) ^ n := by
    rw [Real.mul_self_sqrt (Nat.cast_nonneg _), Nat.cast_pow]
  rw [mul_div_assoc', div_div, hsq]

/-- The `k`-th lag term `d_λ(k) k^{-1/2} M(y·y(k·))` of the limit twist energy. -/
def lagTerm (lam y : ℕ → ℝ) (P k : ℕ) : ℝ := twistDefect lam k / Real.sqrt k * shiftMean y P k

/-- The period means of a periodic profile are bounded by its squared period mass. -/
theorem abs_shiftMean_le {y : ℕ → ℝ} {P : ℕ} (hP : 0 < P) (hy : Function.Periodic y P) (k : ℕ) :
    |shiftMean y P k| ≤ (∑ i ∈ range P, |y i|) ^ 2 := by
  set B := ∑ i ∈ range P, |y i|
  have hyB : ∀ n, |y n| ≤ B := fun n => abs_le_of_periodic hP hy n
  unfold shiftMean periodMean
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  rw [abs_div, abs_of_pos hP0, div_le_iff₀ hP0]
  calc |∑ i ∈ range P, y i * y (k * i)| ≤ ∑ i ∈ range P, B ^ 2 := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
        rw [abs_mul, sq]
        exact mul_le_mul (hyB i) (hyB _) (abs_nonneg _) ((abs_nonneg _).trans (hyB 0))
    _ = B ^ 2 * P := by rw [sum_const, card_range, nsmul_eq_mul, mul_comm]

theorem lagTerm_primeFlip_pow {p : ℕ} (hp : p.Prime) (y : ℕ → ℝ) (P n : ℕ) :
    lagTerm (primeFlipWeight p) y P (p ^ n) =
      (1 - (-1) ^ n) * Real.log p / (p : ℝ) ^ n * shiftMean y P (p ^ n) := by
  unfold lagTerm
  rw [twistDefect_primeFlip_pow hp]

theorem support_lagTerm_primeFlip {p : ℕ} (hp : p.Prime) (y : ℕ → ℝ) (P : ℕ) :
    Function.support (lagTerm (primeFlipWeight p) y P) ⊆ Set.range (fun n : ℕ => p ^ n) := by
  intro k hk
  by_contra hnot
  apply hk
  unfold lagTerm
  rw [twistDefect_primeFlip]
  rcases flip_coeff_cases hp k with h0 | ⟨j, hkj, -⟩
  · rw [h0, zero_div, zero_mul]
  · exact absurd ⟨j + 1, hkj.symm⟩ hnot

theorem summable_lagTerm_primeFlip_pow {p : ℕ} (hp : p.Prime) {y : ℕ → ℝ} {P : ℕ}
    (hP : 0 < P) (hy : Function.Periodic y P) :
    Summable fun n => lagTerm (primeFlipWeight p) y P (p ^ n) := by
  set B := ∑ i ∈ range P, |y i|
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hgeom : Summable fun n : ℕ => (1 / (p : ℝ)) ^ n :=
    summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one (by linarith)]; exact hp1)
  refine Summable.of_norm_bounded (hgeom.mul_left (2 * Real.log p * B ^ 2)) fun n => ?_
  have hlog := Real.log_natCast_nonneg p
  have hpn : (0 : ℝ) < (p : ℝ) ^ n := by positivity
  have h1 : |1 - (-1 : ℝ) ^ n| ≤ 2 := by
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> norm_num
  have hM := abs_shiftMean_le hP hy (p ^ n)
  rw [lagTerm_primeFlip_pow hp, Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_of_pos hpn,
    abs_of_nonneg hlog, _root_.one_div_pow]
  calc |1 - (-1 : ℝ) ^ n| * Real.log p / (p : ℝ) ^ n * |shiftMean y P (p ^ n)|
      ≤ 2 * Real.log p / (p : ℝ) ^ n * B ^ 2 := by gcongr
    _ = 2 * Real.log p * B ^ 2 * (1 / (p : ℝ) ^ n) := by ring

/-- The lag term at the prime power `p^n`. -/
def lagPow (p : ℕ) (y : ℕ → ℝ) (P n : ℕ) : ℝ := lagTerm (primeFlipWeight p) y P (p ^ n)

/-- **The flip energy is explicit.** For a flip at `p` and a `P`-periodic profile `y`,
`2 Σ_k d(k) k^{-1/2} M(y·y(k·)) = 4 log p Σ_j p^{-(2j+1)} M(y·y(p^{2j+1}·))`. -/
theorem twistLimitEnergy_primeFlip {p : ℕ} (hp : p.Prime) {y : ℕ → ℝ} {P : ℕ} (hP : 0 < P)
    (hy : Function.Periodic y P) :
    twistLimitEnergy (primeFlipWeight p) y P = 4 * Real.log p *
      ∑' j : ℕ, shiftMean y P (p ^ (2 * j + 1)) / (p : ℝ) ^ (2 * j + 1) := by
  have hinj : Function.Injective (fun n : ℕ => p ^ n) := Nat.pow_right_injective hp.two_le
  have hreindex : ∑' k, lagTerm (primeFlipWeight p) y P k = ∑' n, lagPow p y P n :=
    (hinj.tsum_eq (support_lagTerm_primeFlip hp y P)).symm
  have hsum : Summable (lagPow p y P) := summable_lagTerm_primeFlip_pow hp hP hy
  have heven : ∀ j, lagPow p y P (2 * j) = 0 := by
    intro j
    rw [lagPow, lagTerm_primeFlip_pow hp, pow_mul, neg_one_sq, one_pow, sub_self, zero_mul,
      zero_div, zero_mul]
  have hodd : ∀ j, lagPow p y P (2 * j + 1) = 2 * Real.log p *
      (shiftMean y P (p ^ (2 * j + 1)) / (p : ℝ) ^ (2 * j + 1)) := by
    intro j
    rw [lagPow, lagTerm_primeFlip_pow hp, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
    ring
  have hinj2 : Function.Injective (fun j : ℕ => 2 * j) := fun a b h => by
    simp only at h; omega
  have hinj21 : Function.Injective (fun j : ℕ => 2 * j + 1) := fun a b h => by
    simp only at h; omega
  have hse : Summable fun j => lagPow p y P (2 * j) := hsum.comp_injective hinj2
  have hso : Summable fun j => lagPow p y P (2 * j + 1) := hsum.comp_injective hinj21
  have hsplit := tsum_even_add_odd (f := lagPow p y P) hse hso
  have htl : twistLimitEnergy (primeFlipWeight p) y P =
      2 * ∑' k, lagTerm (primeFlipWeight p) y P k := rfl
  have h0 : ∑' j, lagPow p y P (2 * j) = 0 := by simp only [heven, tsum_zero]
  have h1 : ∑' j, lagPow p y P (2 * j + 1) = 2 * Real.log p *
      ∑' j, shiftMean y P (p ^ (2 * j + 1)) / (p : ℝ) ^ (2 * j + 1) := by
    simp only [hodd]
    exact tsum_mul_left
  rw [htl, hreindex, ← hsplit, h0, h1]
  ring

/-! ### The resolution–distance law -/

/-- **Resolution needs overlap of the order of the distance.** A twist that is seen, at
square-root distance `D = Σ_k |d_λ(k)|` from `Λ`, is not resolved at any overlap `c` whose pole
energy exceeds `2D(1 + 2c e^c)`: `c ≤ c_0(λ)`. -/
theorem le_resolutionThreshold_of_twistBound_lt {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
    {lam : ℕ → ℝ} (hlam : Summable fun k => |twistDefect lam k|) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hseen : resolutionBottom lam φ c₁ < 0) {c : ℝ} (hc : 0 < c)
    (hlt : twistBound lam c < completedShellEnergy φ c) : c ≤ resolutionThreshold lam φ := by
  have hM := integral_sq_pos_of_noRealZero hφ hsupp hFT
  have hpos : 0 < resolutionBottom lam φ c :=
    lt_of_lt_of_le (by linarith) (completedShellEnergy_sub_le_resolutionBottom hφ hsupp hM hc hlam)
  have hbdd : BddAbove {c : ℝ | 0 < c ∧ 0 < resolutionBottom lam φ c} := by
    refine ⟨c₁, fun c' hc' => ?_⟩
    by_contra hlt'
    push_neg at hlt'
    have := resolutionBottom_antitone hφ hsupp hM hlam hc₁ hlt'.le
    linarith [hc'.2]
  exact le_csSup hbdd ⟨hc, hpos⟩

/-! ### The margin at the threshold is at most twice the distance -/

section Distance

variable {lam : ℕ → ℝ} {φ : ℝ → ℝ}

/-- **The twist energy is bounded by the distance alone.** The limit twist energy of a packet does
not depend on the overlap, so letting `c → 0` in `twistBound λ c` gives
`|E_λ^{twist}| ≤ 2 Σ_k |d_λ(k)| · Σβ²`. -/
theorem abs_twistLimitEnergy_packet_le_distance (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    (hlam : Summable fun k => |twistDefect lam k|) {T : Finset ℕ} (hT : ∀ m ∈ T, 0 < m)
    (β : ℕ → ℝ) :
    |twistLimitEnergy lam (packetProfile T β) (packetPeriod T)| ≤
      2 * (∑' k, |twistDefect lam k|) * ∑ m ∈ T, β m ^ 2 := by
  have hcont : Continuous fun c : ℝ => twistBound lam c * ∑ m ∈ T, β m ^ 2 := by
    unfold twistBound
    fun_prop
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have h0 : twistBound lam 0 * ∑ m ∈ T, β m ^ 2 =
      2 * (∑' k, |twistDefect lam k|) * ∑ m ∈ T, β m ^ 2 := by
    unfold twistBound
    ring
  rw [h0] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact abs_twistLimitEnergy_packet_le hφ hsupp hM hc hlam hT β

/-- The bottom is at least the pole energy minus twice the distance. -/
theorem completedShellEnergy_sub_distance_le_resolutionBottom (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    (hlam : Summable fun k => |twistDefect lam k|) :
    completedShellEnergy φ c - 2 * (∑' k, |twistDefect lam k|) ≤ resolutionBottom lam φ c :=
  le_resolutionBottom fun T hT β hβ => by
    have hE : completedShellEnergy φ c * ∑ m ∈ T, β m ^ 2 ≤
        ∑ m ∈ T, β m ^ 2 * completedConductorEnergy φ c m := by
      rw [mul_sum]
      refine sum_le_sum fun m hm => ?_
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [← completedConductorEnergy_one]
      exact completedConductorEnergy_one_le hφ hsupp hM hc (hT m hm)
    have hG := (abs_le.mp (abs_twistLimitEnergy_packet_le_distance hφ hsupp hM hlam hT β)).1
    rw [hβ, mul_one] at hE hG
    unfold packetEnergy
    linarith

/-- **The resolution–distance law.** Above the threshold of a seen twist at square-root distance
`D = Σ_k |d_λ(k)|`, the pole energy is at most `2D`: `E(c) ≤ 2D` for every `c > c_0(λ)`. -/
theorem completedShellEnergy_le_distance_of_resolutionThreshold_lt (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
    (hlam : Summable fun k => |twistDefect lam k|) {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hseen : resolutionBottom lam φ c₁ < 0) {c : ℝ} (hlt : resolutionThreshold lam φ < c) :
    completedShellEnergy φ c ≤ 2 * (∑' k, |twistDefect lam k|) := by
  have hM := integral_sq_pos_of_noRealZero hφ hsupp hFT
  have hth := (resolutionThreshold_spec hφ hsupp hFT hlam hc₁ hseen).1
  have hc : 0 < c := hth.trans hlt
  by_contra hgt
  push_neg at hgt
  have hpos : 0 < resolutionBottom lam φ c := lt_of_lt_of_le (by linarith)
    (completedShellEnergy_sub_distance_le_resolutionBottom hφ hsupp hM hc hlam)
  have hbdd : BddAbove {c : ℝ | 0 < c ∧ 0 < resolutionBottom lam φ c} := by
    refine ⟨c₁, fun c' hc' => ?_⟩
    by_contra hlt'
    push_neg at hlt'
    have := resolutionBottom_antitone hφ hsupp hM hlam hc₁ hlt'.le
    linarith [hc'.2]
  have : c ≤ resolutionThreshold lam φ := le_csSup hbdd ⟨hc, hpos⟩
  linarith

end Distance

/-! ### The exact threshold of a flip -/

section Threshold

variable {φ : ℝ → ℝ}

/-- **Every flipped prime is seen.** -/
theorem exists_primeFlip_resolutionBottom_neg (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
    {p : ℕ} (hp : p.Prime) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ resolutionBottom (primeFlipWeight p) φ c₁ < 0 := by
  have hM := integral_sq_pos_of_noRealZero hφ hsupp hFT
  have hlam := summable_abs_twistDefect_primeFlip hp
  obtain ⟨c₀, hc₀, hneg⟩ := exists_flip_negative_at_every_large_overlap hφ hsupp hM hp
  obtain ⟨a₀, β₀, hβ₀, hres⟩ :=
    CriticalArithmeticCorrelationTheory.exists_noRealZero_completeWeilEnergy_reserve hφ hsupp
      hFT hc₀
  have hy1 : primeSquareTrial p 1 / Real.sqrt (1 : ℕ) ≠ 0 := by
    have h1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
    have h2 : ¬ p ^ 2 ∣ 1 := fun h => h1 ((dvd_pow_self p two_ne_zero).trans h)
    simp [primeSquareTrial, h1, h2]
  have hle := resolutionBottom_nonpos_of_frequently_neg hφ hsupp hM hc₀ hβ₀ hres hlam
    (y := fun n => primeSquareTrial p n / Real.sqrt n) hy1 (hneg c₀ le_rfl)
  exact ⟨c₀ + 1, by linarith,
    resolutionBottom_neg_of_lt hφ hsupp hFT hlam hc₀ (by linarith) hle⟩

/-- **The exact resolution threshold of a flip.** For every profile without real Fourier zeros
and every prime `p`, the threshold `c_0(ω_p)` is positive and finite; below it the `p`-flipped
complete Weil matrix is eventually positive definite, above it a unit Ramanujan packet makes the
flipped form eventually negative. -/
theorem primeFlip_resolutionThreshold_spec (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
    {p : ℕ} (hp : p.Prime) :
    0 < resolutionThreshold (primeFlipWeight p) φ ∧
      (∀ c, 0 < c → c < resolutionThreshold (primeFlipWeight p) φ →
        ∀ᶠ N : ℕ in atTop, (twistedCompleteWeilMatrix (primeFlipWeight p) φ c N).PosDef) ∧
      (∀ c, resolutionThreshold (primeFlipWeight p) φ < c →
        ∃ T : Finset ℕ, (∀ m ∈ T, 0 < m) ∧ ∃ β : ℕ → ℝ, ∑ m ∈ T, β m ^ 2 = 1 ∧
          ∀ᶠ N : ℕ in atTop, weilQuadTw (primeFlipWeight p)
            (atomicTest N (packetCoeff (packetProfile T β) N) (atomDilate φ (c / N))) < 0) := by
  obtain ⟨c₁, hc₁, hseen⟩ := exists_primeFlip_resolutionBottom_neg hφ hsupp hFT hp
  obtain ⟨h1, -, h3, h4⟩ := resolutionThreshold_spec hφ hsupp hFT
    (summable_abs_twistDefect_primeFlip hp) hc₁ hseen
  exact ⟨h1, h3, h4⟩

/-- **The threshold of a flip grows without bound.** For every `C` there is `p₀` with
`C ≤ c_0(ω_p)` for all primes `p ≥ p₀`: the flip moves the form by at most
`8 log p/√p · (1 + 2C e^C)`, which falls below the pole energy `E(C) > 0`. -/
theorem le_primeFlip_resolutionThreshold (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
    (C : ℝ) : ∃ p₀ : ℕ, ∀ p : ℕ, p.Prime → p₀ ≤ p →
      C ≤ resolutionThreshold (primeFlipWeight p) φ := by
  have hM := integral_sq_pos_of_noRealZero hφ hsupp hFT
  rcases le_or_gt C 0 with hC | hC
  · exact ⟨0, fun p hp _ =>
      hC.trans (primeFlip_resolutionThreshold_spec hφ hsupp hFT hp).1.le⟩
  have hE : 0 < completedShellEnergy φ C := by
    have h1 := CriticalArithmeticCorrelationTheory.completedConductorEnergy_ge_shellTail hφ hsupp
      hM hC one_pos
    rw [completedConductorEnergy_one] at h1
    have h2 := CriticalArithmeticCorrelationTheory.integral_shellSpectrum_pos_of_noRealZero hφ
      hsupp hFT C
    exact lt_of_lt_of_le (mul_pos (div_pos two_pos hM) h2) h1
  set K := 8 * (1 + 2 * C * Real.exp C) with hK
  have hlim := tendsto_log_div_sqrt_natCast.const_mul K
  rw [mul_zero] at hlim
  obtain ⟨p₁, hp₁⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hE))
  refine ⟨max p₁ 4, fun p hp hpp => ?_⟩
  have hp4 : 4 ≤ p := le_of_max_le_right hpp
  have hlam := summable_abs_twistDefect_primeFlip hp
  have hbound : twistBound (primeFlipWeight p) C ≤ K * (Real.log p / Real.sqrt p) := by
    have h := tsum_abs_twistDefect_primeFlip_le hp hp4
    have h0 : 0 ≤ 1 + 2 * C * Real.exp C := by positivity
    unfold twistBound
    calc 2 * (∑' k, |twistDefect (primeFlipWeight p) k|) * (1 + 2 * C * Real.exp C)
        ≤ 2 * (4 * Real.log p / Real.sqrt p) * (1 + 2 * C * Real.exp C) := by gcongr
      _ = K * (Real.log p / Real.sqrt p) := by rw [hK]; ring
  have hpos : 0 < resolutionBottom (primeFlipWeight p) φ C := by
    have h1 := completedShellEnergy_sub_le_resolutionBottom hφ hsupp hM hC hlam
      (lam := primeFlipWeight p)
    have h2 := hp₁ p (le_of_max_le_left hpp)
    linarith
  obtain ⟨c₁, hc₁, hseen⟩ := exists_primeFlip_resolutionBottom_neg hφ hsupp hFT hp
  have hbdd : BddAbove {c : ℝ | 0 < c ∧ 0 < resolutionBottom (primeFlipWeight p) φ c} := by
    refine ⟨c₁, fun c hc => ?_⟩
    by_contra hlt
    push_neg at hlt
    have := resolutionBottom_antitone hφ hsupp hM hlam hc₁ hlt.le
    linarith [hc.2]
  exact le_csSup hbdd ⟨hC, hpos⟩

/-- **The margin at a flip threshold.** For `p ≥ 4`, every overlap above `c_0(ω_p)` has pole
energy at most `8 log p/√p`. -/
theorem completedShellEnergy_le_of_primeFlip_resolutionThreshold_lt (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) {c : ℝ}
    (hlt : resolutionThreshold (primeFlipWeight p) φ < c) :
    completedShellEnergy φ c ≤ 8 * Real.log p / Real.sqrt p := by
  obtain ⟨c₁, hc₁, hseen⟩ := exists_primeFlip_resolutionBottom_neg hφ hsupp hFT hp
  have h := completedShellEnergy_le_distance_of_resolutionThreshold_lt hφ hsupp hFT
    (summable_abs_twistDefect_primeFlip hp) hc₁ hseen hlt
  have hD := tsum_abs_twistDefect_primeFlip_le hp hp4
  have h8 : 2 * (4 * Real.log p / Real.sqrt p) = 8 * Real.log p / Real.sqrt p := by ring
  linarith

/-- **A polynomial lower law for the flip threshold of the tilted spline.** Every overlap `c`
above `c_0(ω_p)` satisfies `C₀ √p ≤ 8 log p · max(c, 1)⁷`, `C₀` the spline's tail constant; so
`c_0(ω_p) ≥ (C₀ √p/(8 log p))^{1/7}` whenever the right side is at least one. -/
theorem tiltedUnitSpline_primeFlip_resolutionThreshold_lower {p : ℕ} (hp : p.Prime)
    (hp4 : 4 ≤ p) {c : ℝ}
    (hlt : resolutionThreshold (primeFlipWeight p) tiltedUnitSpline < c) :
    2 * CriticalArithmeticCorrelationTheory.tiltedSplineTailConstant /
        (∫ u, tiltedUnitSpline u ^ 2) * Real.sqrt p ≤ 8 * Real.log p * max c 1 ^ 7 := by
  have hth := (primeFlip_resolutionThreshold_spec contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero paperFT_tiltedUnitSpline_real_ne_zero hp).1
  have hc : 0 < c := hth.trans hlt
  have hE := completedShellEnergy_le_of_primeFlip_resolutionThreshold_lt contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero paperFT_tiltedUnitSpline_real_ne_zero hp hp4 hlt
  have hfloor : 2 * CriticalArithmeticCorrelationTheory.tiltedSplineTailConstant /
      (∫ u, tiltedUnitSpline u ^ 2) / max c 1 ^ 7 ≤ completedShellEnergy tiltedUnitSpline c := by
    have h := CriticalArithmeticCorrelationTheory.tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor
      (le_max_right c 1) one_pos
    have hanti := completedConductorEnergy_anti contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos hc (le_max_left c 1) one_pos
    simp only [completedConductorEnergy_one] at h hanti
    exact h.trans hanti
  have hm : 0 < max c 1 ^ 7 := pow_pos (lt_of_lt_of_le one_pos (le_max_right c 1)) 7
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have h1 := hfloor.trans hE
  rw [div_le_div_iff₀ hm hsp] at h1
  linarith

/-- The tilted unit spline has no real Fourier zeros, so its flip thresholds are exact. -/
theorem tiltedUnitSpline_primeFlip_resolutionThreshold_spec {p : ℕ} (hp : p.Prime) :
    0 < resolutionThreshold (primeFlipWeight p) tiltedUnitSpline ∧
      (∀ c, 0 < c → c < resolutionThreshold (primeFlipWeight p) tiltedUnitSpline →
        ∀ᶠ N : ℕ in atTop,
          (twistedCompleteWeilMatrix (primeFlipWeight p) tiltedUnitSpline c N).PosDef) ∧
      (∀ c, resolutionThreshold (primeFlipWeight p) tiltedUnitSpline < c →
        ∃ T : Finset ℕ, (∀ m ∈ T, 0 < m) ∧ ∃ β : ℕ → ℝ, ∑ m ∈ T, β m ^ 2 = 1 ∧
          ∀ᶠ N : ℕ in atTop, weilQuadTw (primeFlipWeight p)
            (atomicTest N (packetCoeff (packetProfile T β) N)
              (atomDilate tiltedUnitSpline (c / N))) < 0) :=
  primeFlip_resolutionThreshold_spec contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
    paperFT_tiltedUnitSpline_real_ne_zero hp

end Threshold

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
