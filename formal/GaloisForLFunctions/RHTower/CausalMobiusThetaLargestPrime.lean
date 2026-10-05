import GaloisForLFunctions.RHTower.CausalMobiusThetaUniformCycle

/-!
# The largest-prime normal form of the causal theta observation

With `G(x) = Σ_{m ≥ 1} g(mx)` and the sawtooth observations
`A_N(a, p) = Σ_{r ≥ 0} a_N(r) ψ_p(⌊r/a⌋)`:

* **(14)** exact Abel summation: `A_N(a,p) = N^{−1/2}[(1/p) G(a/N) − G(pa/N)]`;
* the completed-theta reflection `G(1/x) = x G(x)` and the duality
  **(15)** `A_N(a,p) = √N/(pa) [G(N/a) − G(N/(pa))]`;
* **(15a)** `|A_N(a,p)| ≤ C N^{−1/2} e^{−c x²}` for `x = N/(pa) ≥ 1`;
* **(16)** the largest-prime normal form `B(N) = −Σ_p Σ_{a ∣ R_{p−1}} μ(a) A_N(a,p) + e_N + O_A(N^{−A})`,
  also restricted to `p > log N/(4 log log N)`;
* the whole-chain identification of the largest-prime current with the finite Möbius–theta head;
* **(17)** the sieve dilation defect identity, whose constant term has zero theta observation;
* RH equivalences for the largest-prime current, the dilation defect and the head;
* the periodized observer has unbounded uniform-cycle norm.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The lattice sum `G` and its reflection -/

/-- `G(x) = Σ_{m ≥ 1} g(mx)`; the `m = 0` term vanishes because `g(0) = 0`. -/
def thetaLatticeSum (x : ℝ) : ℝ := ∑' m : ℕ, thetaCuspSeed (m * x)

theorem summable_thetaCuspSeed_mul {x : ℝ} (hx : 0 < x) :
    Summable fun m : ℕ => thetaCuspSeed (m * x) := by
  have h := (summable_thetaCuspSourceTerm (Real.log x)).mul_left (Real.exp (Real.log x / 2))⁻¹
  refine h.congr fun m => ?_
  rw [thetaCuspSourceTerm, Real.exp_log hx, ← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]

theorem thetaCuspFullSource_log_eq_lattice {y : ℝ} (hy : 0 < y) :
    thetaCuspFullSource (Real.log y) = Real.sqrt y * thetaLatticeSum y := by
  rw [thetaCuspFullSource, thetaLatticeSum, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [thetaCuspSourceTerm, Real.exp_log hy, exp_log_div_two_eq_sqrt hy]

/-- **Completed-theta reflection**: `G(1/x) = x G(x)` for every `x > 0`. -/
theorem thetaLatticeSum_inv {x : ℝ} (hx : 0 < x) : thetaLatticeSum x⁻¹ = x * thetaLatticeSum x := by
  have h := thetaCuspFullSource_neg (Real.log x)
  rw [← Real.log_inv, thetaCuspFullSource_log_eq_lattice (inv_pos.2 hx),
    thetaCuspFullSource_log_eq_lattice hx, Real.sqrt_inv] at h
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  calc thetaLatticeSum x⁻¹ = Real.sqrt x * ((Real.sqrt x)⁻¹ * thetaLatticeSum x⁻¹) := by
        field_simp
    _ = Real.sqrt x * (Real.sqrt x * thetaLatticeSum x) := by rw [h]
    _ = x * thetaLatticeSum x := by rw [← mul_assoc, Real.mul_self_sqrt hx.le]

/-- A Gaussian majorant of the seed: `|g(t)| ≤ K e^{−π t²/2}`. -/
theorem exists_abs_thetaCuspSeed_le_gauss :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |thetaCuspSeed t| ≤ K * Real.exp (-(Real.pi / 2) * t ^ 2) := by
  set L := Real.exp (Real.pi / 2) * ((Nat.factorial 2 : ℝ) / (Real.pi / 2) ^ 2)
  have hL : 0 ≤ L := by positivity
  refine ⟨(4 * Real.pi ^ 2 + 6 * Real.pi) * L, by positivity, fun t => ?_⟩
  have h1 := abs_thetaCuspSeed_le t
  have h2 := one_add_pow_mul_exp_neg_le (c := Real.pi / 2) (by positivity) 2 (sq_nonneg t)
  have hpoly : 2 * Real.pi * (2 * Real.pi * t ^ 4 + 3 * t ^ 2) ≤
      (4 * Real.pi ^ 2 + 6 * Real.pi) * (1 + t ^ 2) ^ 2 := by
    have := Real.pi_pos
    nlinarith [sq_nonneg t, sq_nonneg (t ^ 2), mul_nonneg this.le (sq_nonneg t),
      mul_nonneg (mul_nonneg this.le this.le) (sq_nonneg t)]
  have hsplit : Real.exp (-Real.pi * t ^ 2) =
      Real.exp (-(Real.pi / 2 * t ^ 2)) * Real.exp (-(Real.pi / 2) * t ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  calc |thetaCuspSeed t| ≤ 2 * Real.pi * (2 * Real.pi * t ^ 4 + 3 * t ^ 2) *
        Real.exp (-Real.pi * t ^ 2) := h1
    _ ≤ (4 * Real.pi ^ 2 + 6 * Real.pi) * (1 + t ^ 2) ^ 2 * Real.exp (-Real.pi * t ^ 2) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = (4 * Real.pi ^ 2 + 6 * Real.pi) * ((1 + t ^ 2) ^ 2 * Real.exp (-(Real.pi / 2 * t ^ 2))) *
          Real.exp (-(Real.pi / 2) * t ^ 2) := by rw [hsplit]; ring
    _ ≤ (4 * Real.pi ^ 2 + 6 * Real.pi) * L * Real.exp (-(Real.pi / 2) * t ^ 2) := by
        gcongr

/-- **Gaussian decay of `G`**: `|G(x)| ≤ C e^{−π x²/2}` for `x ≥ 1`. -/
theorem exists_abs_thetaLatticeSum_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → |thetaLatticeSum x| ≤ C * Real.exp (-(Real.pi / 2) * x ^ 2) := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_thetaCuspSeed_le_gauss
  set r := Real.exp (-(Real.pi / 2))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.2 (by linarith [Real.pi_pos])
  have h1r : 0 < 1 - r := by linarith
  refine ⟨K * (1 - r)⁻¹, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hs := summable_thetaCuspSeed_mul hx0
  rw [thetaLatticeSum, hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, thetaCuspSeed_zero, zero_add]
  have hbound : ∀ m : ℕ, ‖thetaCuspSeed (((m + 1 : ℕ) : ℝ) * x)‖ ≤
      K * Real.exp (-(Real.pi / 2) * x ^ 2) * r ^ m := by
    intro m
    rw [Real.norm_eq_abs]
    refine (hK _).trans ?_
    rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK0
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hpi := Real.pi_pos
    push_cast
    have hx2 : 1 ≤ x ^ 2 := by nlinarith
    have : (m : ℝ) + x ^ 2 ≤ ((m : ℝ) + 1) ^ 2 * x ^ 2 := by
      nlinarith [mul_nonneg hm (sub_nonneg.2 hx2), sq_nonneg ((m : ℝ) * x)]
    nlinarith
  have hsum := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (K * Real.exp (-(Real.pi / 2) * x ^ 2)))
  have := tsum_of_norm_bounded hsum hbound
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  ring

/-! ## (14) Exact Abel summation of a sawtooth observation -/

theorem centeredSawtooth_eq {p : ℕ} (hp : 0 < p) (j : ℕ) :
    centeredSawtooth p j = (j : ℝ) / p - ((j / p : ℕ) : ℝ) - ((p : ℝ) - 1) / (2 * p) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have h := Nat.mod_add_div j p
  have hR : ((j % p : ℕ) : ℝ) = j - p * ((j / p : ℕ) : ℝ) := by
    have : ((j % p : ℕ) : ℝ) + p * ((j / p : ℕ) : ℝ) = j := by exact_mod_cast h
    linarith
  rw [centeredSawtooth, hR]
  field_simp

/-- The jump of the centered sawtooth: `ψ_p(j+1) − ψ_p(j) = 1/p − 1_{p ∣ j+1}`. -/
theorem centeredSawtooth_succ_sub {p : ℕ} (hp : 0 < p) (j : ℕ) :
    centeredSawtooth p (j + 1) - centeredSawtooth p j = 1 / p - if p ∣ j + 1 then 1 else 0 := by
  rw [centeredSawtooth_eq hp, centeredSawtooth_eq hp, Nat.succ_div]
  split_ifs <;> push_cast <;> ring

/-- The sawtooth observed through the floor `⌊r/a⌋` jumps only on multiples of `a`. -/
theorem centeredSawtooth_div_succ_sub {p a : ℕ} (hp : 0 < p) (r : ℕ) :
    centeredSawtooth p ((r + 1) / a) - centeredSawtooth p (r / a) =
      if a ∣ r + 1 then (1 : ℝ) / p - (if p ∣ (r + 1) / a then (1 : ℝ) else 0) else 0 := by
  rw [Nat.succ_div]
  split_ifs with h1 h2
  · rw [centeredSawtooth_succ_sub hp, if_pos h2]
  · rw [centeredSawtooth_succ_sub hp, if_neg h2]
  · simp

theorem summable_thetaIncrement_mul_bounded {N : ℕ} (hN : 1 ≤ N) {φ : ℕ → ℝ} {C : ℝ}
    (hφ : ∀ r, |φ r| ≤ C) : Summable fun r => thetaIncrement N r * φ r :=
  Summable.of_norm_bounded ((summable_abs_thetaIncrement hN).mul_right C) fun r => by
    rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hφ r) (abs_nonneg _)

/-- **(14)** `A_N(a,p) = N^{−1/2}[(1/p) Σ_{j≥1} g(ja/N) − Σ_{k≥1} g(kpa/N)]`. -/
theorem sawtoothObservation_eq_lattice {N a p : ℕ} (hN : 1 ≤ N) (ha : 0 < a) (hp : 0 < p) :
    sawtoothObservation N a p =
      (Real.sqrt N)⁻¹ * ((1 / p) * thetaLatticeSum (a / N) - thetaLatticeSum (p * a / N)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set u : ℕ → ℝ := fun r => thetaCuspSeed (r / N) / Real.sqrt N with hu_def
  set φ : ℕ → ℝ := fun r => centeredSawtooth p (r / a) with hφ_def
  have hu : Summable u := (summable_thetaCuspSeed_div hN).div_const _
  have hu0 : u 0 = 0 := by simp [u, thetaCuspSeed_zero]
  have hφb : ∀ r, |φ r| ≤ 1 := fun r => abs_centeredSawtooth_le hp _
  have hinc : ∀ r, thetaIncrement N r = u r - u (r + 1) := fun r => by
    simp only [thetaIncrement, u]; push_cast; ring
  have huφ : Summable fun r => u r * φ r :=
    Summable.of_norm_bounded (hu.abs.mul_right 1) fun r => by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hφb r) (abs_nonneg _)
  have hu1φ : Summable fun r => u (r + 1) * φ r :=
    Summable.of_norm_bounded (((summable_nat_add_iff 1).2 hu).abs.mul_right 1) fun r => by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hφb r) (abs_nonneg _)
  -- summation by parts
  have hA : sawtoothObservation N a p = ∑' r, u (r + 1) * (φ (r + 1) - φ r) := by
    rw [sawtoothObservation]
    simp_rw [hinc, sub_mul]
    rw [huφ.tsum_sub hu1φ, huφ.tsum_eq_zero_add, hu0, zero_mul, zero_add,
      ← (((summable_nat_add_iff 1).2 huφ)).tsum_sub hu1φ]
    exact tsum_congr fun r => by ring
  -- the jump function, supported on multiples of `a`
  set F : ℕ → ℝ := fun n => if a ∣ n then (1 : ℝ) / p - (if p ∣ n / a then (1 : ℝ) else 0) else 0
    with hF
  have hjump : ∀ r, φ (r + 1) - φ r = F (r + 1) := fun r => centeredSawtooth_div_succ_sub hp r
  have hB : ∑' r, u (r + 1) * (φ (r + 1) - φ r) = ∑' n, u n * F n := by
    simp_rw [hjump]
    have hs : Summable fun n => u n * F n := by
      refine Summable.of_norm_bounded (hu.abs.mul_right 2) fun n => ?_
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hp1 : (1 : ℝ) / p ≤ 1 := by
        rw [div_le_one (by exact_mod_cast hp)]; exact_mod_cast hp
      have hp0 : (0 : ℝ) ≤ 1 / p := by positivity
      simp only [F]
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith
    rw [hs.tsum_eq_zero_add, hu0, zero_mul, zero_add]
  -- reindex over the multiples `n = a j`
  have hC : ∑' n, u n * F n = ∑' j, u (a * j) * (1 / p - if p ∣ j then 1 else 0) := by
    rw [← (Function.Injective.tsum_eq (g := fun j => a * j) (mul_right_injective₀ ha.ne') ?_)]
    · refine tsum_congr fun j => ?_
      simp only [F, if_pos (dvd_mul_right a j), Nat.mul_div_cancel_left j ha]
    · intro n hn
      by_contra hnr
      apply hn
      have : ¬ a ∣ n := fun ⟨j, hj⟩ => hnr ⟨j, hj.symm⟩
      simp [F, this]
  have hx1 : (0 : ℝ) < a / N := by have : (0 : ℝ) < a := by exact_mod_cast ha
                                   positivity
  have hx2 : (0 : ℝ) < p * a / N := by have : (0 : ℝ) < a := by exact_mod_cast ha
                                       have : (0 : ℝ) < p := by exact_mod_cast hp
                                       positivity
  have hua : ∀ j : ℕ, u (a * j) = thetaCuspSeed (j * (a / N)) / Real.sqrt N := fun j => by
    simp only [u]; push_cast; ring_nf
  have hsa : Summable fun j : ℕ => u (a * j) := by
    simp_rw [hua]; exact (summable_thetaCuspSeed_mul hx1).div_const _
  have hD : ∑' j, u (a * j) * (if p ∣ j then 1 else 0) = ∑' k, u (a * (p * k)) := by
    rw [← (Function.Injective.tsum_eq (g := fun k => p * k) (mul_right_injective₀ hp.ne') ?_)]
    · exact tsum_congr fun k => by simp
    · intro j hj
      by_contra hjr
      apply hj
      have : ¬ p ∣ j := fun ⟨k, hk⟩ => hjr ⟨k, hk.symm⟩
      simp [this]
  have hsD : Summable fun j => u (a * j) * (if p ∣ j then 1 else 0) :=
    Summable.of_norm_bounded (hsa.abs.mul_right 1) fun j => by
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      split_ifs <;> simp
  rw [hA, hB, hC]
  simp_rw [mul_sub]
  rw [(hsa.mul_right _).tsum_sub hsD, hD, tsum_mul_right]
  have hup : ∀ k : ℕ, u (a * (p * k)) = thetaCuspSeed (k * (p * a / N)) / Real.sqrt N := fun k => by
    simp only [u]; push_cast; ring_nf
  simp_rw [hup, hua]
  rw [tsum_div_const, tsum_div_const, thetaLatticeSum, thetaLatticeSum]
  ring

/-- **(15)** The source-specific duality `A_N(a,p) = √N/(pa) [G(N/a) − G(N/(pa))]`. -/
theorem sawtoothObservation_eq_dual {N a p : ℕ} (hN : 1 ≤ N) (ha : 0 < a) (hp : 0 < p) :
    sawtoothObservation N a p =
      Real.sqrt N / (p * a) * (thetaLatticeSum (N / a) - thetaLatticeSum (N / (p * a))) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [sawtoothObservation_eq_lattice hN ha hp]
  have h1 : thetaLatticeSum (a / N) = N / a * thetaLatticeSum (N / a) := by
    rw [← thetaLatticeSum_inv (by positivity), inv_div]
  have h2 : thetaLatticeSum (p * a / N) = N / (p * a) * thetaLatticeSum (N / (p * a)) := by
    rw [← thetaLatticeSum_inv (by positivity), inv_div]
  rw [h1, h2]
  conv_rhs => rw [← Real.div_sqrt (x := (N : ℝ))]
  ring

theorem le_exp_inv_pi_add (x : ℝ) : x ≤ Real.exp (1 / Real.pi + Real.pi / 4 * x ^ 2) := by
  have hpi := Real.pi_pos
  have h1 : x ≤ 1 / Real.pi + Real.pi / 4 * x ^ 2 := by
    have : 0 ≤ (Real.pi * x / 2 - 1) ^ 2 := sq_nonneg _
    have h2 : Real.pi * (1 / Real.pi + Real.pi / 4 * x ^ 2 - x) = (Real.pi * x / 2 - 1) ^ 2 := by
      field_simp; ring
    nlinarith
  linarith [Real.add_one_le_exp (1 / Real.pi + Real.pi / 4 * x ^ 2)]

/-- **(15a)** `|A_N(a,p)| ≤ C N^{−1/2} e^{−π x²/4}` with `x = N/(pa) ≥ 1`. -/
theorem exists_abs_sawtoothObservation_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N a p : ℕ, 1 ≤ N → 0 < a → 0 < p → p * a ≤ N →
      |sawtoothObservation N a p| ≤
        C * (Real.sqrt N)⁻¹ * Real.exp (-(Real.pi / 4) * ((N : ℝ) / (p * a)) ^ 2) := by
  obtain ⟨CG, hCG0, hCG⟩ := exists_abs_thetaLatticeSum_le
  refine ⟨2 * CG * Real.exp (1 / Real.pi), by positivity, fun N a p hN ha hp hpa => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  set x : ℝ := (N : ℝ) / (p * a) with hx_def
  have hpaR : (0 : ℝ) < p * a := by positivity
  have hx1 : 1 ≤ x := by
    rw [hx_def, le_div_iff₀ hpaR, one_mul]; exact_mod_cast hpa
  have hNa : (N : ℝ) / a = p * x := by rw [hx_def]; field_simp
  have hpx : x ≤ (N : ℝ) / a := by rw [hNa]; nlinarith
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  have hpre : Real.sqrt N / (p * a) = x * (Real.sqrt N)⁻¹ := by
    rw [hx_def]
    conv_lhs => rw [← Real.div_sqrt (x := (N : ℝ))]
    ring
  have hG1 : |thetaLatticeSum ((N : ℝ) / a)| ≤ CG * Real.exp (-(Real.pi / 2) * x ^ 2) := by
    refine (hCG _ (hx1.trans hpx)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCG0)
    have : x ^ 2 ≤ ((N : ℝ) / a) ^ 2 := pow_le_pow_left₀ (by linarith) hpx 2
    nlinarith [Real.pi_pos]
  have hG2 := hCG x hx1
  have hxe : x * Real.exp (-(Real.pi / 2) * x ^ 2) ≤
      Real.exp (1 / Real.pi) * Real.exp (-(Real.pi / 4) * x ^ 2) := by
    have h := le_exp_inv_pi_add x
    have : x * Real.exp (-(Real.pi / 2) * x ^ 2) ≤
        Real.exp (1 / Real.pi + Real.pi / 4 * x ^ 2) * Real.exp (-(Real.pi / 2) * x ^ 2) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    refine this.trans (le_of_eq ?_)
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [sawtoothObservation_eq_dual hN ha hp, hpre, abs_mul, abs_mul, abs_of_nonneg (by linarith),
    abs_of_pos (inv_pos.2 hs0)]
  calc x * (Real.sqrt N)⁻¹ * |thetaLatticeSum (N / a) - thetaLatticeSum (N / (p * a))| ≤
        x * (Real.sqrt N)⁻¹ * (2 * CG * Real.exp (-(Real.pi / 2) * x ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (abs_sub _ _).trans ?_
        rw [← hx_def]; linarith
    _ = 2 * CG * (Real.sqrt N)⁻¹ * (x * Real.exp (-(Real.pi / 2) * x ^ 2)) := by ring
    _ ≤ 2 * CG * (Real.sqrt N)⁻¹ * (Real.exp (1 / Real.pi) * Real.exp (-(Real.pi / 4) * x ^ 2)) :=
        mul_le_mul_of_nonneg_left hxe (by positivity)
    _ = 2 * CG * Real.exp (1 / Real.pi) * (Real.sqrt N)⁻¹ * Real.exp (-(Real.pi / 4) * x ^ 2) := by
        ring

/-! ## (16) The largest-prime normal form -/

/-- The signed largest-prime current `Σ_{p ≤ N} Σ_{a ∣ R_{p−1}, pa ≤ N} μ(a) A_N(a, p)`. -/
def largestPrimeCurrent (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
    ∑ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N),
      ((ArithmeticFunction.moebius a : ℤ) : ℝ) * sawtoothObservation N a p

/-- `H_p(X) = 1` when `1 ≤ X ≤ p`: no `p`-rough integer other than `1` is at most `p`. -/
theorem roughMoebiusSum_eq_one_of_le {p X : ℕ} (hX : 1 ≤ X) (hXp : X ≤ p) : roughMoebiusSum p X = 1 := by
  rw [roughMoebiusSum, Finset.sum_eq_single 1]
  · simp
  · intro b hb hb1
    obtain ⟨hbI, hbr⟩ := Finset.mem_filter.1 hb
    obtain ⟨hb1', hbX⟩ := Finset.mem_Icc.1 hbI
    obtain ⟨q, hq, hqb⟩ := Nat.exists_prime_and_dvd hb1
    have := hbr q (Nat.mem_primeFactors.2 ⟨hq, hqb, by omega⟩)
    have := Nat.le_of_dvd (by omega) hqb
    omega
  · intro h1
    exact absurd (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, hX⟩, by simp⟩) h1

theorem abs_roughMoebiusSum_sub_one_le (p X : ℕ) : |roughMoebiusSum p X - 1| ≤ 2 + X := by
  have h := abs_roughMoebiusSum_le p X
  have hlog : Real.log X ≤ X := by
    rcases Nat.eq_zero_or_pos X with rfl | hX
    · simp
    · have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < X by exact_mod_cast hX)
      linarith
  calc |roughMoebiusSum p X - 1| ≤ |roughMoebiusSum p X| + |(1 : ℝ)| := abs_sub _ _
    _ ≤ 2 + X := by rw [abs_one]; linarith

theorem log_div_le_sqrt {N : ℕ} (hN : 1 ≤ N) : Real.log N / (4 * Real.log 2) ≤ Real.sqrt N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := Real.sqrt_pos.2 hNR
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have h1 : Real.log (Real.sqrt N) ≤ Real.sqrt N - 1 := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hNR.le] at h1
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- `x ≥ log N/(4 log 2)` whenever `x ≥ p` and `x ≥ N/(pa)` with `a ∣ R_{p−1}`: either
`4^p ≤ √N`, so `x ≥ N/R_p ≥ √N`, or `p > log N/(4 log 2)`. -/
theorem log_div_le_of_primorial {N p a : ℕ} (hN : 1 ≤ N) (hp : p.Prime) (ha : a ∣ primorial (p - 1))
    {y : ℝ} (hyp : (p : ℝ) ≤ y) (hyN : (N : ℝ) / (p * a) ≤ y) : Real.log N / (4 * Real.log 2) ≤ y := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha (primorial_pos _)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpa : ((p * a : ℕ) : ℝ) ≤ (4 : ℝ) ^ p := by
    have h1 : p * a ≤ primorial p := by
      rw [primorial_prime_eq hp]; exact Nat.mul_le_mul_left p (Nat.le_of_dvd (primorial_pos _) ha)
    have h2 := primorial_le_four_pow p
    exact_mod_cast h1.trans h2
  push_cast at hpa
  have hpa0 : (0 : ℝ) < p * a := by have := hp.pos; positivity
  by_cases h4 : (4 : ℝ) ^ p ≤ Real.sqrt N
  · have hs := Real.sqrt_pos.2 hNR
    have : Real.sqrt N ≤ (N : ℝ) / (p * a) := by
      rw [le_div_iff₀ hpa0]
      calc Real.sqrt N * (p * a) ≤ Real.sqrt N * Real.sqrt N :=
            mul_le_mul_of_nonneg_left (hpa.trans h4) hs.le
        _ = N := Real.mul_self_sqrt hNR.le
    exact (log_div_le_sqrt hN).trans (this.trans hyN)
  · have hlt : Real.log (Real.sqrt N) < Real.log ((4 : ℝ) ^ p) :=
      Real.log_lt_log (Real.sqrt_pos.2 hNR) (not_le.1 h4)
    rw [Real.log_sqrt hNR.le, Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlt
    push_cast at hlt
    rw [div_le_iff₀ (by linarith)]
    nlinarith

/-- `N^k e^{−c y²} ≤ C N^{−A}` uniformly for `y ≥ κ log N`. -/
theorem exists_pow_mul_exp_neg_sq_le {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) (k : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ y : ℝ, κ * Real.log N ≤ y →
      (N : ℝ) ^ k * Real.exp (-c * y ^ 2) ≤ C * (N : ℝ) ^ (-A) := by
  refine ⟨Real.exp ((k + A) ^ 2 / (4 * c * κ ^ 2)), (Real.exp_pos _).le, fun N hN y hy => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set L := Real.log N with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hN)
  have hy0 : 0 ≤ κ * L := by positivity
  have hy2 : (κ * L) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have hNk : (N : ℝ) ^ k = Real.exp (k * L) := by
    rw [Real.exp_nat_mul, hL, Real.exp_log hNR]
  have hNA : (N : ℝ) ^ (-A) = Real.exp (-A * L) := by
    rw [Real.rpow_def_of_pos hNR, hL]; ring_nf
  rw [hNk, hNA, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hq : (k + A) * L - c * κ ^ 2 * L ^ 2 ≤ (k + A) ^ 2 / (4 * c * κ ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * c * κ ^ 2 * L - (k + A))]
  nlinarith

theorem card_divisors_filter_le {N p : ℕ} (hp : 0 < p) :
    ((primorial (p - 1)).divisors.filter (fun a => p * a ≤ N)).card ≤ N := by
  calc _ ≤ (Finset.Icc 1 N).card := Finset.card_le_card fun a ha => by
          obtain ⟨ha1, haN⟩ := Finset.mem_filter.1 ha
          exact Finset.mem_Icc.2 ⟨Nat.pos_of_mem_divisors ha1, (Nat.le_mul_of_pos_left a hp).trans haN⟩
    _ = N := by simp

/-- Counting: the double sum over `(p, a)` has at most `N²` terms. -/
theorem abs_sum_primes_divisors_le {N : ℕ} {f : ℕ → ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      ∀ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N), |f p a| ≤ B) :
    |∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ∑ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N), f p a| ≤ (N : ℝ) ^ 2 * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      |∑ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N), f p a| ≤ N * B := by
    intro p hp
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_card_nsmul _ _ B (hf p hp)).trans ?_)
    rw [nsmul_eq_mul]
    have hcard := card_divisors_filter_le (N := N) (Nat.Prime.pos (Finset.mem_filter.1 hp).2)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
  refine (Finset.sum_le_card_nsmul _ _ _ h1).trans ?_
  rw [nsmul_eq_mul, sq, mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have : ((Finset.Icc 1 N).filter Nat.Prime).card ≤ N := (Finset.card_filter_le _ _).trans (by simp)
  exact_mod_cast this

/-- **(16)** The largest-prime normal form: for every `A`,
`B(N) = −Σ_{p ≤ N} Σ_{a ∣ R_{p−1}, pa ≤ N} μ(a) A_N(a,p) + e_N + O_A(N^{−A})`. -/
theorem exists_abs_causalMobiusThetaTail_sub_largestPrimeCurrent_le (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |causalMobiusThetaTail N - (-largestPrimeCurrent N + thetaCellDefect N)| ≤ C * (N : ℝ) ^ (-A) := by
  obtain ⟨C1, hC10, hC1⟩ := exists_abs_sawtoothObservation_le
  have hκ : (0 : ℝ) < 1 / (4 * Real.log 2) := by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
                                                 positivity
  obtain ⟨C2, hC20, hC2⟩ := exists_pow_mul_exp_neg_sq_le (c := Real.pi / 4) (by positivity) hκ 3 A
  refine ⟨3 * C1 * C2, by positivity, fun N hN => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hdiff : causalMobiusThetaTail N - (-largestPrimeCurrent N + thetaCellDefect N) =
      -∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ∑ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N),
          ((ArithmeticFunction.moebius a : ℤ) : ℝ) * (roughMoebiusSum p (N / (p * a)) - 1) *
            sawtoothObservation N a p := by
    rw [causalMobiusThetaTail_natCast_eq_smoothRough hN, largestPrimeCurrent]
    simp only [mul_sub, sub_mul, mul_one, Finset.sum_sub_distrib]
    ring
  rw [hdiff, abs_neg]
  have hB : 0 ≤ 3 * C1 * C2 * (N : ℝ) ^ (-A) / (N : ℝ) ^ 2 := by positivity
  refine (abs_sum_primes_divisors_le hB fun p hp a ha => ?_).trans (le_of_eq (by field_simp))
  obtain ⟨hp1, hpp⟩ := Finset.mem_filter.1 hp
  obtain ⟨ha1, haN⟩ := Finset.mem_filter.1 ha
  have ha0 : 0 < a := Nat.pos_of_mem_divisors ha1
  have hpa0 : 0 < p * a := Nat.mul_pos hpp.pos ha0
  have hX1 : 1 ≤ N / (p * a) := (Nat.le_div_iff_mul_le hpa0).2 (by simpa using haN)
  by_cases hXp : N / (p * a) ≤ p
  · rw [roughMoebiusSum_eq_one_of_le hX1 hXp, sub_self, mul_zero, zero_mul, abs_zero]
    exact hB
  · push Not at hXp
    set x : ℝ := (N : ℝ) / (p * a) with hx_def
    have hXx : ((N / (p * a) : ℕ) : ℝ) ≤ x := by
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := p * a)
      push_cast at this
      exact this
    have hpx : (p : ℝ) ≤ x := by
      have : ((p : ℕ) : ℝ) + 1 ≤ ((N / (p * a) : ℕ) : ℝ) := by exact_mod_cast hXp
      linarith
    have hκx : 1 / (4 * Real.log 2) * Real.log N ≤ x := by
      rw [one_div_mul_eq_div]
      exact log_div_le_of_primorial hN hpp (Nat.dvd_of_mem_divisors ha1) hpx le_rfl
    have hexp := hC2 N hN x hκx
    have hA := hC1 N a p hN ha0 hpp.pos haN
    rw [← hx_def] at hA
    have hH : |roughMoebiusSum p (N / (p * a)) - 1| ≤ 3 * N := by
      refine (abs_roughMoebiusSum_sub_one_le _ _).trans ?_
      have : ((N / (p * a) : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self _ _
      linarith
    have hμ : |((ArithmeticFunction.moebius a : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hsq : (Real.sqrt N)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hN1)
    rw [abs_mul, abs_mul]
    calc |((ArithmeticFunction.moebius a : ℤ) : ℝ)| * |roughMoebiusSum p (N / (p * a)) - 1| *
          |sawtoothObservation N a p| ≤ 1 * (3 * N) * (C1 * 1 * Real.exp (-(Real.pi / 4) * x ^ 2)) := by
          gcongr
          refine hA.trans ?_
          gcongr
      _ = 3 * C1 * ((N : ℝ) ^ 3 * Real.exp (-(Real.pi / 4) * x ^ 2)) / (N : ℝ) ^ 2 := by
          field_simp
      _ ≤ 3 * C1 * (C2 * (N : ℝ) ^ (-A)) / (N : ℝ) ^ 2 := by gcongr
      _ = 3 * C1 * C2 * (N : ℝ) ^ (-A) / (N : ℝ) ^ 2 := by ring

/-! ## Restriction to `p > P`, `P = log N/(4 log log N)` -/

/-- The low-prime threshold `P(N) = log N/(4 log log N)`. -/
def lowPrimeThreshold (N : ℕ) : ℝ := Real.log N / (4 * Real.log (Real.log N))

theorem four_pow_le_sqrt_of_le_lowPrimeThreshold {N p : ℕ} (hN : 8 ≤ N)
    (hp : (p : ℝ) ≤ lowPrimeThreshold N) : (4 : ℝ) ^ p ≤ Real.sqrt N := by
  have hNR : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogN : 2 ≤ Real.log N := by
    have : Real.log 8 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at this
    push_cast at this
    linarith
  have hll : Real.log 2 ≤ Real.log (Real.log N) := Real.log_le_log (by norm_num) hlogN
  have hll0 : 0 < Real.log (Real.log N) := by linarith
  rw [← exp_log_div_two_eq_sqrt hN0, ← Real.rpow_natCast,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), Real.exp_le_exp,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  rw [lowPrimeThreshold, le_div_iff₀ (by positivity)] at hp
  push_cast
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  -- `2 log 2 · p ≤ 2 log 2 · log N/(4 log log N) ≤ log N/2`
  have h1 : (p : ℝ) * (4 * Real.log 2) ≤ Real.log N := by
    calc (p : ℝ) * (4 * Real.log 2) ≤ (p : ℝ) * (4 * Real.log (Real.log N)) := by gcongr
      _ ≤ Real.log N := hp
  nlinarith

/-- **Low primes are negligible**: for every `A`, the `p ≤ P(N)` part of the largest-prime
current is `O_A(N^{−A})`. -/
theorem exists_abs_lowPrimeCurrent_le (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 8 ≤ N →
      |∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun p : ℕ => (p : ℝ) ≤ lowPrimeThreshold N),
        ∑ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N),
          ((ArithmeticFunction.moebius a : ℤ) : ℝ) * sawtoothObservation N a p| ≤ C * (N : ℝ) ^ (-A) := by
  obtain ⟨C1, hC10, hC1⟩ := exists_abs_sawtoothObservation_le
  have hκ : (0 : ℝ) < 1 / (4 * Real.log 2) := by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
                                                 positivity
  obtain ⟨C2, hC20, hC2⟩ := exists_pow_mul_exp_neg_sq_le (c := Real.pi / 4) (by positivity) hκ 2 A
  refine ⟨C1 * C2, by positivity, fun N hN8 => ?_⟩
  have hN : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Finset.sum_filter]
  have hB : 0 ≤ C1 * C2 * (N : ℝ) ^ (-A) / (N : ℝ) ^ 2 := by positivity
  refine (abs_sum_primes_divisors_le (f := fun p a => if (p : ℝ) ≤ lowPrimeThreshold N then
      ((ArithmeticFunction.moebius a : ℤ) : ℝ) * sawtoothObservation N a p else 0) hB
    fun p hp a ha => ?_).trans (le_of_eq (by field_simp)) |>.trans' (le_of_eq ?_)
  · split_ifs with hpP
    · obtain ⟨hp1, hpp⟩ := Finset.mem_filter.1 hp
      obtain ⟨ha1, haN⟩ := Finset.mem_filter.1 ha
      have ha0 : 0 < a := Nat.pos_of_mem_divisors ha1
      have had := Nat.dvd_of_mem_divisors ha1
      set x : ℝ := (N : ℝ) / (p * a) with hx_def
      have hpa0 : (0 : ℝ) < p * a := by have := hpp.pos; positivity
      have hpa4 : (p : ℝ) * a ≤ (4 : ℝ) ^ p := by
        have h1 : p * a ≤ primorial p := by
          rw [primorial_prime_eq hpp]; exact Nat.mul_le_mul_left p (Nat.le_of_dvd (primorial_pos _) had)
        exact_mod_cast h1.trans (primorial_le_four_pow p)
      have hsx : Real.sqrt N ≤ x := by
        rw [hx_def, le_div_iff₀ hpa0]
        calc Real.sqrt N * (p * a) ≤ Real.sqrt N * Real.sqrt N :=
              mul_le_mul_of_nonneg_left (hpa4.trans (four_pow_le_sqrt_of_le_lowPrimeThreshold hN8 hpP))
                (Real.sqrt_nonneg _)
          _ = N := Real.mul_self_sqrt hNR.le
      have hκx : 1 / (4 * Real.log 2) * Real.log N ≤ x := by
        rw [one_div_mul_eq_div]; exact (log_div_le_sqrt hN).trans hsx
      have hexp := hC2 N hN x hκx
      have hA := hC1 N a p hN ha0 hpp.pos haN
      rw [← hx_def] at hA
      have hμ : |((ArithmeticFunction.moebius a : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hsq : (Real.sqrt N)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hN1)
      rw [abs_mul]
      calc |((ArithmeticFunction.moebius a : ℤ) : ℝ)| * |sawtoothObservation N a p| ≤
            1 * (C1 * 1 * Real.exp (-(Real.pi / 4) * x ^ 2)) := by
            gcongr
            refine hA.trans ?_
            gcongr
        _ = C1 * ((N : ℝ) ^ 2 * Real.exp (-(Real.pi / 4) * x ^ 2)) / (N : ℝ) ^ 2 := by
            field_simp
        _ ≤ C1 * (C2 * (N : ℝ) ^ (-A)) / (N : ℝ) ^ 2 := by gcongr
        _ = C1 * C2 * (N : ℝ) ^ (-A) / (N : ℝ) ^ 2 := by ring
    · rw [abs_zero]; exact hB
  · congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp

/-- **(16) restricted to `p > P`**: for `N ≥ 8` and every `A`,
`B(N) = −Σ_{P < p ≤ N} Σ_{a ∣ R_{p−1}, pa ≤ N} μ(a) A_N(a,p) + e_N + O_A(N^{−A})`. -/
theorem exists_abs_causalMobiusThetaTail_sub_highPrimeCurrent_le (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 8 ≤ N →
      |causalMobiusThetaTail N -
        (-(∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun p : ℕ => lowPrimeThreshold N < p),
            ∑ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N),
              ((ArithmeticFunction.moebius a : ℤ) : ℝ) * sawtoothObservation N a p) +
          thetaCellDefect N)| ≤ C * (N : ℝ) ^ (-A) := by
  obtain ⟨C1, hC10, hC1⟩ := exists_abs_causalMobiusThetaTail_sub_largestPrimeCurrent_le A
  obtain ⟨C2, hC20, hC2⟩ := exists_abs_lowPrimeCurrent_le A
  refine ⟨C1 + C2, by positivity, fun N hN8 => ?_⟩
  have hN : 1 ≤ N := by omega
  have hsplit := Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 N).filter Nat.Prime)
    (fun p : ℕ => (p : ℝ) ≤ lowPrimeThreshold N) (fun p => ∑ a ∈ (primorial (p - 1)).divisors.filter
      (fun a => p * a ≤ N), ((ArithmeticFunction.moebius a : ℤ) : ℝ) * sawtoothObservation N a p)
  simp only [not_le] at hsplit
  have h1 := hC1 N hN
  have h2 := hC2 N hN8
  rw [largestPrimeCurrent, ← hsplit] at h1
  calc _ = |(causalMobiusThetaTail N - (-(∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter
          (fun p : ℕ => (p : ℝ) ≤ lowPrimeThreshold N), ∑ a ∈ (primorial (p - 1)).divisors.filter
            (fun a => p * a ≤ N), ((ArithmeticFunction.moebius a : ℤ) : ℝ) * sawtoothObservation N a p +
          ∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun p : ℕ => lowPrimeThreshold N < p),
            ∑ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N),
              ((ArithmeticFunction.moebius a : ℤ) : ℝ) * sawtoothObservation N a p) +
          thetaCellDefect N)) - ∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter
          (fun p : ℕ => (p : ℝ) ≤ lowPrimeThreshold N), ∑ a ∈ (primorial (p - 1)).divisors.filter
            (fun a => p * a ≤ N), ((ArithmeticFunction.moebius a : ℤ) : ℝ) * sawtoothObservation N a p| := by
          congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ C1 * (N : ℝ) ^ (-A) + C2 * (N : ℝ) ^ (-A) := add_le_add h1 h2
    _ = (C1 + C2) * (N : ℝ) ^ (-A) := by ring

/-! ## Whole-chain check: the finite Möbius–theta head -/

/-- Every squarefree `d ≥ 2` is `d = pa` for exactly one prime `p` (its largest prime factor) with
`a ∣ R_{p−1}`; non-squarefree `d` carry `μ(d) = 0`. -/
theorem sum_primes_divisors_moebius_eq {N : ℕ} (F : ℕ → ℝ) :
    ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ∑ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N),
          ((ArithmeticFunction.moebius (p * a) : ℤ) : ℝ) * F (p * a) =
      ∑ d ∈ Finset.Icc 2 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * F d := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.1 * x.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, a⟩ hx _
    obtain ⟨hp, ha⟩ := Finset.mem_sigma.1 hx
    have hpp := (Finset.mem_filter.1 hp).2
    obtain ⟨ha1, haN⟩ := Finset.mem_filter.1 ha
    have ha0 : 0 < a := Nat.pos_of_mem_divisors ha1
    exact Finset.mem_Icc.2 ⟨hpp.two_le.trans (Nat.le_mul_of_pos_right p ha0), haN⟩
  · rintro ⟨p, a⟩ hx _ ⟨p', a'⟩ hx' _ heq
    obtain ⟨hp, ha⟩ := Finset.mem_sigma.1 hx
    obtain ⟨hp', ha'⟩ := Finset.mem_sigma.1 hx'
    have hpp := (Finset.mem_filter.1 hp).2
    have hpp' := (Finset.mem_filter.1 hp').2
    have ha1 := Nat.dvd_of_mem_divisors (Finset.mem_filter.1 ha).1
    have ha1' := Nat.dvd_of_mem_divisors (Finset.mem_filter.1 ha').1
    simp only at heq
    have key : ∀ {p a p' a' : ℕ}, p.Prime → p'.Prime → a ∣ primorial (p - 1) →
        p * a = p' * a' → ¬ p < p' := by
      intro p a p' a' hp hp' ha h hlt
      have hdvd : p' ∣ p * a := h ▸ dvd_mul_right p' a'
      rcases (Nat.Prime.dvd_mul hp').1 hdvd with h1 | h1
      · have := (Nat.prime_dvd_prime_iff_eq hp' hp).1 h1
        omega
      · have := prime_le_of_dvd_primorial hp' (h1.trans ha)
        omega
    have hpq : p = p' := by
      rcases lt_trichotomy p p' with h | h | h
      · exact absurd h (key hpp hpp' ha1 heq)
      · exact h
      · exact absurd h (key hpp' hpp ha1' heq.symm)
    subst hpq
    have haa : a = a' := Nat.eq_of_mul_eq_mul_left hpp.pos heq
    subst haa
    rfl
  · intro d hd hne
    obtain ⟨hd2, hdN⟩ := Finset.mem_Icc.1 hd
    have hμ : ArithmeticFunction.moebius d ≠ 0 := fun h => hne (by simp [h])
    have hsq := ArithmeticFunction.moebius_ne_zero_iff_squarefree.1 hμ
    have hne' : d.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
    set p := d.primeFactors.max' hne' with hp_def
    have hpmem := Finset.max'_mem _ hne'
    rw [← hp_def] at hpmem
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hpmem
    set a := d / p with ha_def
    have hda : d = p * a := (Nat.mul_div_cancel' hpd).symm
    have ha : a ∣ primorial (p - 1) := by
      have hsqa : Squarefree a := hsq.squarefree_of_dvd ⟨p, by rw [hda]; ring⟩
      refine DeletionResidueMartingale.squarefree_dvd_primorial hsqa fun q hq => ?_
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hqa := Nat.dvd_of_mem_primeFactors hq
      have hqd : q ∈ d.primeFactors :=
        Nat.mem_primeFactors.2 ⟨hqp, hqa.trans ⟨p, by rw [hda]; ring⟩, by omega⟩
      have hle : q ≤ p := Finset.le_max' _ _ hqd
      have hqne : q ≠ p := by
        intro hqe
        rw [hqe] at hqa
        exact not_squarefree_of_mul_self_dvd hpp (by rw [hda]; exact Nat.mul_dvd_mul_left p hqa) hsq
      omega
    refine ⟨⟨p, a⟩, Finset.mem_sigma.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hpp.one_lt.le, ?_⟩, hpp⟩,
      Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨ha, (primorial_pos _).ne'⟩, ?_⟩⟩, ?_, hda.symm⟩
    · exact (Nat.le_of_dvd (by omega) hpd).trans hdN
    · rw [← hda]; exact hdN
    · simp only; rw [← hda]; exact hne
  · rintro ⟨p, a⟩ _ _
    rfl

/-- `√N/d · G(N/d) = d^{−1/2} k(log(N/d))`. -/
theorem sqrt_div_mul_thetaLatticeSum_eq {N d : ℕ} (hN : 1 ≤ N) (hd : 0 < d) :
    Real.sqrt N / d * thetaLatticeSum (N / d) =
      (d : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource (Real.log (N / d)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hdR.le
  rw [thetaCuspFullSource_log_eq_lattice (by positivity), Real.sqrt_div' _ hdR.le, Real.rpow_neg hdR.le,
    ← Real.sqrt_eq_rpow, ← mul_assoc, inv_mul_eq_div, div_div, hs]

/-- The finite Möbius–theta head `Σ_{2 ≤ d ≤ N} μ(d) d^{−1/2} k(log(N/d))`. -/
def mobiusThetaHead (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    ((d : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource (Real.log (N / d)))

/-- **Whole-chain check**: up to `O_A(N^{−A})`, the largest-prime current is the finite
Möbius–theta head over `2 ≤ d ≤ N`; so `−(current)` is the negative head. -/
theorem exists_abs_largestPrimeCurrent_sub_mobiusThetaHead_le (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |largestPrimeCurrent N - mobiusThetaHead N| ≤ C * (N : ℝ) ^ (-A) := by
  obtain ⟨CG, hCG0, hCG⟩ := exists_abs_thetaLatticeSum_le
  have hκ : (0 : ℝ) < 1 / (4 * Real.log 2) := by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
                                                 positivity
  obtain ⟨C2, hC20, hC2⟩ := exists_pow_mul_exp_neg_sq_le (c := Real.pi / 2) (by positivity) hκ 3 A
  refine ⟨CG * C2, by positivity, fun N hN => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set F : ℕ → ℝ := fun d => (d : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource (Real.log (N / d))
  have hterm : ∀ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      ∀ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N),
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) * sawtoothObservation N a p =
          ((ArithmeticFunction.moebius a : ℤ) : ℝ) * (Real.sqrt N / (p * a) * thetaLatticeSum (N / a)) +
            ((ArithmeticFunction.moebius (p * a) : ℤ) : ℝ) * F (p * a) := by
    intro p hp a ha
    have hpp := (Finset.mem_filter.1 hp).2
    have ha1 := Finset.mem_filter.1 ha |>.1
    have ha0 : 0 < a := Nat.pos_of_mem_divisors ha1
    have hμ := moebius_smooth_rough (b := 1) hpp (Nat.dvd_of_mem_divisors ha1) one_pos (by simp)
    rw [mul_one] at hμ
    have h2 := sqrt_div_mul_thetaLatticeSum_eq hN (Nat.mul_pos hpp.pos ha0)
    push_cast at h2
    simp only [F]
    rw [sawtoothObservation_eq_dual hN ha0 hpp.pos, hμ]
    push_cast
    rw [← h2]
    simp
    ring
  have hLPC : largestPrimeCurrent N =
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
        ∑ a ∈ (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N),
          ((ArithmeticFunction.moebius a : ℤ) : ℝ) * (Real.sqrt N / (p * a) * thetaLatticeSum (N / a))) +
        mobiusThetaHead N := by
    rw [largestPrimeCurrent, mobiusThetaHead, ← sum_primes_divisors_moebius_eq F, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a ha => hterm p hp a ha
  rw [hLPC, add_sub_cancel_right]
  have hB : 0 ≤ CG * C2 * (N : ℝ) ^ (-A) / (N : ℝ) ^ 2 := by positivity
  refine (abs_sum_primes_divisors_le hB fun p hp a ha => ?_).trans (le_of_eq (by field_simp))
  obtain ⟨-, hpp⟩ := Finset.mem_filter.1 hp
  obtain ⟨ha1, haN⟩ := Finset.mem_filter.1 ha
  have ha0 : 0 < a := Nat.pos_of_mem_divisors ha1
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  set y : ℝ := (N : ℝ) / a with hy_def
  have hpy : (p : ℝ) ≤ y := by
    rw [hy_def, le_div_iff₀ haR]; exact_mod_cast haN
  have hyN : (N : ℝ) / (p * a) ≤ y := by
    rw [hy_def]
    exact div_le_div_of_nonneg_left hNR.le haR (by nlinarith)
  have hκy : 1 / (4 * Real.log 2) * Real.log N ≤ y := by
    rw [one_div_mul_eq_div]; exact log_div_le_of_primorial hN hpp (Nat.dvd_of_mem_divisors ha1) hpy hyN
  have hexp := hC2 N hN y hκy
  have hG := hCG y (by linarith)
  have hμ : |((ArithmeticFunction.moebius a : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hpre : Real.sqrt N / (p * a) ≤ N := by
    have h1 : Real.sqrt N ≤ N := by
      have hs1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN1
      nlinarith [Real.mul_self_sqrt hNR.le]
    have ha1R : (1 : ℝ) ≤ a := by exact_mod_cast ha0
    have h2 : (1 : ℝ) ≤ p * a := by nlinarith
    exact (div_le_self (Real.sqrt_nonneg _) h2).trans h1
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt N / (p * a))]
  calc |((ArithmeticFunction.moebius a : ℤ) : ℝ)| * (Real.sqrt N / (p * a) * |thetaLatticeSum y|) ≤
        1 * (N * (CG * Real.exp (-(Real.pi / 2) * y ^ 2))) := by
        gcongr
    _ = CG * ((N : ℝ) ^ 3 * Real.exp (-(Real.pi / 2) * y ^ 2)) / (N : ℝ) ^ 2 := by
        field_simp
    _ ≤ CG * (C2 * (N : ℝ) ^ (-A)) / (N : ℝ) ^ 2 := by gcongr
    _ = CG * C2 * (N : ℝ) ^ (-A) / (N : ℝ) ^ 2 := by ring

/-! ## (17) The sieve dilation defect -/

/-- The truncated wheel count `S_{p,X}(r) = Σ_{a ∣ R_{p−1}, a ≤ X} μ(a) ⌊r/a⌋`. -/
def wheelCount (p X r : ℕ) : ℝ :=
  ∑ a ∈ (primorial (p - 1)).divisors.filter (· ≤ X),
    ((ArithmeticFunction.moebius a : ℤ) : ℝ) * ((r / a : ℕ) : ℝ)

/-- `M_{p,X} = Σ_{a ∣ R_{p−1}, a ≤ X} μ(a)`. -/
def wheelMoebiusSum (p X : ℕ) : ℝ :=
  ∑ a ∈ (primorial (p - 1)).divisors.filter (· ≤ X), ((ArithmeticFunction.moebius a : ℤ) : ℝ)

/-- **(17)** `Σ_{a ∣ R_{p−1}, a ≤ X} μ(a) ψ_p(⌊r/a⌋) = S_{p,X}(r)/p − S_{p,X}(⌊r/p⌋) − (p−1)/(2p) M_{p,X}`,
from `j mod p = j − p⌊j/p⌋` and `⌊⌊r/a⌋/p⌋ = ⌊⌊r/p⌋/a⌋`. -/
theorem sum_moebius_centeredSawtooth_eq_dilationDefect {p : ℕ} (hp : 0 < p) (X r : ℕ) :
    ∑ a ∈ (primorial (p - 1)).divisors.filter (· ≤ X),
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) * centeredSawtooth p (r / a) =
      wheelCount p X r / p - wheelCount p X (r / p) -
        ((p : ℝ) - 1) / (2 * p) * wheelMoebiusSum p X := by
  rw [wheelCount, wheelCount, wheelMoebiusSum, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [centeredSawtooth_eq hp, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm a p]
  ring

theorem filter_le_div_eq_filter_mul_le {p N : ℕ} (hp : 0 < p) (s : Finset ℕ) :
    s.filter (· ≤ N / p) = s.filter (fun a => p * a ≤ N) :=
  Finset.filter_congr fun a _ => by rw [Nat.le_div_iff_mul_le hp, mul_comm]

/-- The constant term is invisible: `Σ_{r ≥ 0} a_N(r) c = 0`. -/
theorem tsum_thetaIncrement_mul_const {N : ℕ} (hN : 1 ≤ N) (c : ℝ) :
    ∑' r, thetaIncrement N r * c = 0 := by
  rw [tsum_mul_right, (hasSum_thetaIncrement hN).tsum_eq, zero_mul]

/-- The cross-prime scale defect `S_{p,N/p}(r)/p − S_{p,N/p}(⌊r/p⌋)`. -/
def dilationDefect (N p r : ℕ) : ℝ := wheelCount p (N / p) r / p - wheelCount p (N / p) (r / p)

/-- The largest-prime current is the wavelet observation of the complete cross-prime sieve
dilation defect, summed over primes. -/
theorem largestPrimeCurrent_eq_dilationDefect {N : ℕ} (hN : 1 ≤ N) :
    largestPrimeCurrent N = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
      ∑' r, thetaIncrement N r * dilationDefect N p r := by
  rw [largestPrimeCurrent]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp := (Finset.mem_filter.1 hp).2
  set S := (primorial (p - 1)).divisors.filter (fun a => p * a ≤ N)
  set μR : ℕ → ℝ := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)
  have hS : (primorial (p - 1)).divisors.filter (· ≤ N / p) = S :=
    filter_le_div_eq_filter_mul_le hpp.pos _
  have hsum : ∀ a ∈ S, Summable fun r => μR a * (thetaIncrement N r * centeredSawtooth p (r / a)) :=
    fun a _ => (summable_thetaIncrement_mul_bounded hN (fun r => abs_centeredSawtooth_le hpp.pos _)).mul_left _
  have h1 : ∑ a ∈ S, μR a * sawtoothObservation N a p =
      ∑' r, thetaIncrement N r * ∑ a ∈ S, μR a * centeredSawtooth p (r / a) := by
    simp_rw [sawtoothObservation, ← tsum_mul_left]
    rw [← Summable.tsum_finsetSum hsum]
    refine tsum_congr fun r => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [h1]
  set c := ((p : ℝ) - 1) / (2 * p) * wheelMoebiusSum p (N / p)
  have h17 : ∀ r, ∑ a ∈ S, μR a * centeredSawtooth p (r / a) = dilationDefect N p r - c := by
    intro r
    rw [← hS, sum_moebius_centeredSawtooth_eq_dilationDefect hpp.pos, dilationDefect]
  have hbd : ∀ r, |∑ a ∈ S, μR a * centeredSawtooth p (r / a)| ≤ S.card := by
    intro r
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ a ∈ S, |μR a * centeredSawtooth p (r / a)| ≤ 1 := by
      intro a _
      rw [abs_mul]
      have hμ : |μR a| ≤ 1 := by
        simp only [μR]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have := abs_centeredSawtooth_le hpp.pos (r / a)
      nlinarith [abs_nonneg (μR a), abs_nonneg (centeredSawtooth p (r / a))]
    refine (Finset.sum_le_card_nsmul _ _ 1 this).trans ?_
    simp
  have hs0 : Summable fun r => thetaIncrement N r * ∑ a ∈ S, μR a * centeredSawtooth p (r / a) :=
    summable_thetaIncrement_mul_bounded hN hbd
  have hs2 : Summable fun r => thetaIncrement N r * c := (summable_abs_thetaIncrement hN).of_abs.mul_right c
  have hs1 : Summable fun r => thetaIncrement N r * dilationDefect N p r := by
    refine (hs0.add hs2).congr fun r => ?_
    rw [h17]; ring
  simp_rw [h17, mul_sub]
  rw [hs1.tsum_sub hs2, tsum_thetaIncrement_mul_const hN, sub_zero]

/-! ## Consequences for RH -/

theorem exists_abs_causalMobiusThetaTail_add_largestPrimeCurrent_le :
    ∃ D : ℝ, ∀ N : ℕ, 1 ≤ N → |causalMobiusThetaTail N - -largestPrimeCurrent N| ≤ D := by
  obtain ⟨C0, hC00, hC0⟩ := exists_abs_causalMobiusThetaTail_sub_largestPrimeCurrent_le 0
  obtain ⟨Ce, hCe0, hCe⟩ := exists_abs_thetaCellDefect_le
  refine ⟨C0 + Ce, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 := hC0 N hN
  rw [neg_zero, Real.rpow_zero, mul_one] at h1
  have h2 : |thetaCellDefect N| ≤ Ce := by
    refine (hCe N hN).trans (div_le_self hCe0 ?_)
    have : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN1
    nlinarith
  calc |causalMobiusThetaTail N - -largestPrimeCurrent N| =
        |(causalMobiusThetaTail N - (-largestPrimeCurrent N + thetaCellDefect N)) + thetaCellDefect N| := by
        ring_nf
    _ ≤ |causalMobiusThetaTail N - (-largestPrimeCurrent N + thetaCellDefect N)| + |thetaCellDefect N| :=
        abs_add_le _ _
    _ ≤ C0 + Ce := add_le_add h1 h2

/-- RH holds iff the signed largest-prime current has subpower growth. -/
theorem riemannHypothesis_iff_largestPrimeCurrent_subpower :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |largestPrimeCurrent N| ≤ C * (N : ℝ) ^ ε := by
  obtain ⟨D, hD⟩ := exists_abs_causalMobiusThetaTail_add_largestPrimeCurrent_le
  rw [riemannHypothesis_iff_causalMobiusThetaTail_nat_subpower]
  constructor
  · intro hB ε hε
    obtain ⟨C, hC⟩ := hB ε hε
    refine ⟨max C 0 + |D|, fun N hN => ?_⟩
    have := natPowerBound_of_abs_sub_le (g := fun N => -largestPrimeCurrent N) hε.le hD hC N hN
    rwa [abs_neg] at this
  · intro hL ε hε
    obtain ⟨C, hC⟩ := hL ε hε
    exact ⟨_, natPowerBound_of_abs_sub_le (f := fun N => -largestPrimeCurrent N) hε.le
      (fun N hN => by rw [abs_sub_comm]; exact hD N hN) (fun N hN => by rw [abs_neg]; exact hC N hN)⟩

/-- RH holds iff the wavelet observation of the cross-prime sieve dilation defect, summed over
primes, has subpower growth. -/
theorem riemannHypothesis_iff_dilationDefect_subpower :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ∑' r, thetaIncrement N r * dilationDefect N p r| ≤
        C * (N : ℝ) ^ ε := by
  rw [riemannHypothesis_iff_largestPrimeCurrent_subpower]
  refine forall₂_congr fun ε _ => exists_congr fun C => forall₂_congr fun N hN => ?_
  rw [largestPrimeCurrent_eq_dilationDefect hN]

/-- RH holds iff the finite Möbius–theta head over `2 ≤ d ≤ N` has subpower growth. -/
theorem riemannHypothesis_iff_mobiusThetaHead_subpower :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |mobiusThetaHead N| ≤ C * (N : ℝ) ^ ε := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_largestPrimeCurrent_sub_mobiusThetaHead_le 0
  have hD' : ∀ N : ℕ, 1 ≤ N → |largestPrimeCurrent N - mobiusThetaHead N| ≤ D := fun N hN => by
    have := hD N hN; rwa [neg_zero, Real.rpow_zero, mul_one] at this
  rw [riemannHypothesis_iff_largestPrimeCurrent_subpower]
  constructor
  · intro hL ε hε
    obtain ⟨C, hC⟩ := hL ε hε
    exact ⟨_, natPowerBound_of_abs_sub_le hε.le hD' hC⟩
  · intro hH ε hε
    obtain ⟨C, hC⟩ := hH ε hε
    exact ⟨_, natPowerBound_of_abs_sub_le hε.le (fun N hN => by rw [abs_sub_comm]; exact hD' N hN) hC⟩

/-! ## The uniform carrier has no free Hilbert bound -/

theorem abs_thetaCuspSeed_inv_natCast_ge {N : ℕ} (hN : 2 ≤ N) :
    2 * Real.pi * Real.exp (-Real.pi) / (N : ℝ) ^ 2 ≤ |thetaCuspSeed (1 / N)| := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set t : ℝ := 1 / N with ht
  have ht0 : 0 < t := by positivity
  have ht2 : t ^ 2 ≤ 1 / 4 := by
    rw [ht, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_four
  have hpoly : t ^ 2 ≤ 3 * t ^ 2 - 2 * Real.pi * t ^ 4 := by
    have h1 : 2 * Real.pi * t ^ 2 ≤ 2 := by nlinarith
    have h2 : 0 ≤ t ^ 2 := sq_nonneg t
    nlinarith
  have hexp : Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * t ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg t])
  have heq : |thetaCuspSeed t| =
      2 * Real.pi * (3 * t ^ 2 - 2 * Real.pi * t ^ 4) * Real.exp (-Real.pi * t ^ 2) := by
    rw [thetaCuspSeed, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_nonpos (by nlinarith [sq_nonneg t])]
    ring
  rw [heq]
  have hN2 : 1 / (N : ℝ) ^ 2 = t ^ 2 := by rw [ht, div_pow, one_pow]
  calc 2 * Real.pi * Real.exp (-Real.pi) / (N : ℝ) ^ 2 = 2 * Real.pi * t ^ 2 * Real.exp (-Real.pi) := by
        rw [← hN2]; ring
    _ ≤ 2 * Real.pi * (3 * t ^ 2 - 2 * Real.pi * t ^ 4) * Real.exp (-Real.pi * t ^ 2) := by
        have hnn : 0 ≤ 3 * t ^ 2 - 2 * Real.pi * t ^ 4 := by linarith [sq_nonneg t]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by positivity)) hexp (Real.exp_pos _).le
          (mul_nonneg (by positivity) hnn)

theorem abs_thetaIncrement_le_of_inv_cube {Cg : ℝ} (hCg0 : 0 ≤ Cg)
    (hCg : ∀ x : ℝ, 0 < x → |thetaCuspSeed x| ≤ Cg * (x ^ 3)⁻¹) {N r : ℕ} (hN : 1 ≤ N) (hr : 1 ≤ r) :
    |thetaIncrement N r| ≤ 2 * Cg * (N : ℝ) ^ 3 / (r : ℝ) ^ 3 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hs1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 (by exact_mod_cast hN)
  have h1 := hCg ((r : ℝ) / N) (by positivity)
  have h2 := hCg (((r : ℝ) + 1) / N) (by positivity)
  have hinv1 : (((r : ℝ) / N) ^ 3)⁻¹ = (N : ℝ) ^ 3 / (r : ℝ) ^ 3 := by
    rw [div_pow, inv_div]
  have hinv2 : ((((r : ℝ) + 1) / N) ^ 3)⁻¹ ≤ (N : ℝ) ^ 3 / (r : ℝ) ^ 3 := by
    rw [div_pow, inv_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (by positivity) (by linarith) 3)
  rw [thetaIncrement, abs_div, abs_of_pos (Real.sqrt_pos.2 hNR)]
  refine (div_le_self (abs_nonneg _) hs1).trans ((abs_sub _ _).trans ?_)
  rw [hinv1] at h1
  calc |thetaCuspSeed (r / N)| + |thetaCuspSeed ((r + 1) / N)| ≤
        Cg * ((N : ℝ) ^ 3 / (r : ℝ) ^ 3) + Cg * ((N : ℝ) ^ 3 / (r : ℝ) ^ 3) :=
        add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left hinv2 hCg0))
    _ = 2 * Cg * (N : ℝ) ^ 3 / (r : ℝ) ^ 3 := by ring

/-- **The uniform carrier gives no free Hilbert bound**: on `M = R_N` the periodized observer has
`⟨Q_N, Q_N⟩_M → ∞`, although the physical theta test stays bounded. -/
theorem tendsto_cyclePairing_periodizedObserver_self :
    Tendsto (fun N : ℕ => cyclePairing (primorial N) (periodizedObserver (primorial N) N)
      (periodizedObserver (primorial N) N)) atTop atTop := by
  obtain ⟨Cg, hCg0, hCg⟩ := exists_abs_thetaCuspSeed_le_inv_cube
  set Z : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3
  have hZs : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 3 := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 3))
    exact this.congr fun k => by push_cast; rfl
  have hZ0 : 0 ≤ Z := tsum_nonneg fun k => by positivity
  set c₀ : ℝ := 2 * Real.pi * Real.exp (-Real.pi)
  have hc₀ : 0 < c₀ := by positivity
  refine tendsto_atTop_mono' atTop ?_
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by positivity : 0 < c₀ ^ 2 / 4))
  filter_upwards [DeletionResidueMartingale.eventually_rpow_le_primorial 6, eventually_ge_atTop 2,
    eventually_ge_atTop ⌈4 * Cg * Z / c₀⌉₊] with N hM hN2 hNK
  set M := primorial N
  have hN : 1 ≤ N := by omega
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < N := by linarith
  have hM6 : (N : ℝ) ^ 6 ≤ M := by
    have := hM; rw [show ((6 : ℝ)) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this; exact this
  have hMpos : 0 < M := primorial_pos N
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hs := Real.sqrt_pos.2 hN0
  have hsN : Real.sqrt N ≤ N := by
    have : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 (by linarith)
    nlinarith [Real.mul_self_sqrt hN0.le]
  -- the zero-residue progression sum
  set S : ℝ := ∑' k, thetaIncrement N (0 + M * k)
  have hsum : Summable fun k => thetaIncrement N (0 + M * k) :=
    (summable_abs_thetaIncrement hN).of_abs.comp_injective (i := fun k => 0 + M * k)
      fun k₁ k₂ h => by simpa [hMpos.ne'] using h
  have hS : S = thetaIncrement N 0 + ∑' k, thetaIncrement N (M * (k + 1)) := by
    show ∑' k, thetaIncrement N (0 + M * k) = _
    rw [hsum.tsum_eq_zero_add]; simp
  have hhead : c₀ / ((N : ℝ) ^ 2 * Real.sqrt N) ≤ |thetaIncrement N 0| := by
    rw [thetaIncrement_zero, abs_neg, abs_div, abs_of_pos hs, ← div_div]
    exact div_le_div_of_nonneg_right (abs_thetaCuspSeed_inv_natCast_ge hN2) hs.le
  have hb : ∀ k : ℕ, ‖thetaIncrement N (M * (k + 1))‖ ≤
      2 * Cg * (N : ℝ) ^ 3 / (M : ℝ) ^ 3 * (1 / ((k : ℝ) + 1) ^ 3) := by
    intro k
    rw [Real.norm_eq_abs]
    refine (abs_thetaIncrement_le_of_inv_cube hCg0 hCg hN (Nat.mul_pos hMpos k.succ_pos)).trans
      (le_of_eq ?_)
    push_cast
    field_simp
  have htail := tsum_of_norm_bounded (hZs.hasSum.mul_left (2 * Cg * (N : ℝ) ^ 3 / (M : ℝ) ^ 3)) hb
  rw [Real.norm_eq_abs] at htail
  have hK : 4 * Cg * Z ≤ c₀ * N := by
    have h1 : 4 * Cg * Z / c₀ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNK)
    calc 4 * Cg * Z = 4 * Cg * Z / c₀ * c₀ := by field_simp
      _ ≤ N * c₀ := mul_le_mul_of_nonneg_right h1 hc₀.le
      _ = c₀ * N := mul_comm _ _
  have hM3 : (N : ℝ) ^ 18 ≤ (M : ℝ) ^ 3 := by
    calc (N : ℝ) ^ 18 = ((N : ℝ) ^ 6) ^ 3 := by ring
      _ ≤ (M : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hM6 3
  have htail' : 2 * Cg * (N : ℝ) ^ 3 / (M : ℝ) ^ 3 * Z ≤ c₀ / (2 * ((N : ℝ) ^ 2 * Real.sqrt N)) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hN7 : (N : ℝ) ^ 7 ≤ (N : ℝ) ^ 18 := pow_le_pow_right₀ (by linarith) (by norm_num)
    calc 2 * Cg * (N : ℝ) ^ 3 * Z * (2 * ((N : ℝ) ^ 2 * Real.sqrt N)) =
          4 * Cg * Z * ((N : ℝ) ^ 5 * Real.sqrt N) := by ring
      _ ≤ 4 * Cg * Z * ((N : ℝ) ^ 5 * N) := by gcongr
      _ = 4 * Cg * Z * (N : ℝ) ^ 6 := by ring
      _ ≤ c₀ * N * (N : ℝ) ^ 6 := by gcongr
      _ = c₀ * (N : ℝ) ^ 7 := by ring
      _ ≤ c₀ * (N : ℝ) ^ 18 := by gcongr
      _ ≤ c₀ * (M : ℝ) ^ 3 := by gcongr
  have hSlow : c₀ / (2 * ((N : ℝ) ^ 2 * Real.sqrt N)) ≤ |S| := by
    rw [hS]
    have h3 : |thetaIncrement N 0| - |∑' k, thetaIncrement N (M * (k + 1))| ≤
        |thetaIncrement N 0 + ∑' k, thetaIncrement N (M * (k + 1))| := by
      have := abs_sub_abs_le_abs_sub (thetaIncrement N 0) (-∑' k, thetaIncrement N (M * (k + 1)))
      rwa [abs_neg, sub_neg_eq_add] at this
    have h4 : c₀ / ((N : ℝ) ^ 2 * Real.sqrt N) = 2 * (c₀ / (2 * ((N : ℝ) ^ 2 * Real.sqrt N))) := by
      field_simp
    linarith
  -- the uniform norm dominates the zero residue
  have hpair : (M : ℝ) * S ^ 2 ≤ cyclePairing M (periodizedObserver M N) (periodizedObserver M N) := by
    rw [cyclePairing]
    have h0 := Finset.single_le_sum (f := fun a => periodizedObserver M N a * periodizedObserver M N a)
      (s := Finset.range M) (fun a _ => mul_self_nonneg _) (Finset.mem_range.2 hMpos)
    have hQ0 : periodizedObserver M N 0 = M * S := rfl
    simp only [hQ0] at h0
    calc (M : ℝ) * S ^ 2 = (M : ℝ)⁻¹ * ((M * S) * (M * S)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h0 (by positivity)
  refine le_trans ?_ hpair
  have hsq : (c₀ / (2 * ((N : ℝ) ^ 2 * Real.sqrt N))) ^ 2 = c₀ ^ 2 / (4 * (N : ℝ) ^ 5) := by
    rw [div_pow]
    congr 1
    rw [mul_pow, mul_pow, Real.sq_sqrt hN0.le]; ring
  have hS2 : c₀ ^ 2 / (4 * (N : ℝ) ^ 5) ≤ S ^ 2 := by
    rw [← hsq, ← sq_abs S]; exact pow_le_pow_left₀ (by positivity) hSlow 2
  calc c₀ ^ 2 / 4 * (N : ℝ) = (N : ℝ) ^ 6 * (c₀ ^ 2 / (4 * (N : ℝ) ^ 5)) := by field_simp
    _ ≤ (M : ℝ) * S ^ 2 := mul_le_mul hM6 hS2 (by positivity) hM0.le

end

end RHTower
