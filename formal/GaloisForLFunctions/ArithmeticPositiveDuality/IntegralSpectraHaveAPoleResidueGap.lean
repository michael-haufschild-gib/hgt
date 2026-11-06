import GaloisForLFunctions.ArithmeticPositiveDuality.IntegrableDefectsAtUnitDensityAreRigid

/-!
# A residue gap for positive integral spectra

An integrable Riemann functional-equation defect leaves the atomic Abel spectrum unchanged.
Three-point positivity forbids distinct atoms within unit distance when the residue is less
than √2. Integral masses then equal one, and the Abel density is at most one.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FreqHamburger
open RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The squared norm of `r - exp(ix) - exp(iy)` gives three-point positivity. -/
private theorem three_point_cosine (r x y : ℝ) :
    2 * r * (Real.cos x + Real.cos y) ≤ r ^ 2 + 2 + 2 * Real.cos (x - y) := by
  rw [Real.cos_sub]
  nlinarith only [sq_nonneg (r - Real.cos x - Real.cos y),
    sq_nonneg (Real.sin x + Real.sin y), Real.sin_sq_add_cos_sq x,
    Real.sin_sq_add_cos_sq y]

/-- The three-point Gram inequality for the positive Abel measure. -/
theorem abelCos_three_point {a lam : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hlam : ∀ n, 1 ≤ lam n)
    (ha : Summable fun n => a n / lam n ^ 2)
    (r p q : ℝ) {ε : ℝ} (hε : 0 < ε) :
    2 * r * (abelCos a lam p ε + abelCos a lam q ε) ≤
      (r ^ 2 + 2) * abelCos a lam 0 ε + 2 * abelCos a lam (q - p) ε := by
  let w : ℕ → ℝ := fun n => a n * Real.exp (-(2 * Real.pi * lam n * ε))
  have hw : ∀ n, 0 ≤ w n := fun n => mul_nonneg (ha0 n) (Real.exp_pos _).le
  have sw : Summable w := summable_abelWeight hlam ha0 ha hε
  have sp := summable_abelCos hlam ha0 ha p hε
  have sq := summable_abelCos hlam ha0 ha q hε
  have sd := summable_abelCos hlam ha0 ha (q - p) hε
  have hpoint : ∀ n,
      2 * r * (w n * Real.cos (2 * Real.pi * lam n * p) +
        w n * Real.cos (2 * Real.pi * lam n * q)) ≤
      (r ^ 2 + 2) * w n + 2 * (w n * Real.cos (2 * Real.pi * lam n * (q - p))) := by
    intro n
    have ht := three_point_cosine r (2 * Real.pi * lam n * q) (2 * Real.pi * lam n * p)
    rw [show 2 * Real.pi * lam n * q - 2 * Real.pi * lam n * p =
      2 * Real.pi * lam n * (q - p) by ring] at ht
    have hh := mul_le_mul_of_nonneg_left ht (hw n)
    nlinarith only [hh]
  have hs := ((sp.add sq).mul_left (2 * r)).tsum_le_tsum hpoint
    ((sw.mul_left (r ^ 2 + 2)).add (sd.mul_left 2))
  rw [tsum_mul_left, sp.tsum_add sq, (sw.mul_left (r ^ 2 + 2)).tsum_add (sd.mul_left 2),
    tsum_mul_left, tsum_mul_left] at hs
  have hh := mul_le_mul_of_nonneg_left hs hε.le
  dsimp only [w] at hh
  simp only [abelCos, mul_zero, Real.cos_zero, mul_one]
  convert hh using 1 <;> ring

/-- A spectrum with unit masses and gaps at least one has Abel density at most one. -/
theorem abelCos_zero_le_of_nat_le {lam : ℕ → ℝ}
    (hlam : ∀ n : ℕ, (n : ℝ) + 1 ≤ lam n) {ε : ℝ} (hε : 0 < ε) :
    abelCos (fun _ => 1) lam 0 ε ≤ 1 / (2 * Real.pi) := by
  let r : ℝ := Real.exp (-(2 * Real.pi * ε))
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))
  have hg := summable_geometric_of_lt_one hr0.le hr1
  have hterm : ∀ n, Real.exp (-(2 * Real.pi * lam n * ε)) ≤ r * r ^ n := by
    intro n
    calc Real.exp (-(2 * Real.pi * lam n * ε)) ≤
        Real.exp (-((n : ℝ) + 1) * (2 * Real.pi * ε)) := by
          apply Real.exp_le_exp.mpr
          nlinarith only [mul_le_mul_of_nonneg_right (hlam n)
            (mul_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) hε.le)]
      _ = r * r ^ n := by
          rw [show -((n : ℝ) + 1) * (2 * Real.pi * ε) =
            -(2 * Real.pi * ε) + (n : ℝ) * (-(2 * Real.pi * ε)) by ring,
            Real.exp_add, Real.exp_nat_mul]
  have hs : Summable fun n => Real.exp (-(2 * Real.pi * lam n * ε)) :=
    (hg.mul_left r).of_nonneg_of_le (fun n => (Real.exp_pos _).le) hterm
  have hb : (∑' n, Real.exp (-(2 * Real.pi * lam n * ε))) ≤ r / (1 - r) := by
    have hh := hs.tsum_le_tsum hterm (hg.mul_left r)
    rwa [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1, ← div_eq_mul_inv] at hh
  have he : Real.exp (2 * Real.pi * ε) * r = 1 := by
    dsimp only [r]
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hc : (1 + 2 * Real.pi * ε) * r ≤ 1 := by
    have hadd : 1 + 2 * Real.pi * ε ≤ Real.exp (2 * Real.pi * ε) := by
      simpa only [add_comm] using Real.add_one_le_exp (2 * Real.pi * ε)
    calc (1 + 2 * Real.pi * ε) * r ≤ Real.exp (2 * Real.pi * ε) * r :=
          mul_le_mul_of_nonneg_right hadd hr0.le
      _ = 1 := he
  simp only [abelCos, one_mul, mul_zero, Real.cos_zero, mul_one]
  calc ε * (∑' n, Real.exp (-(2 * Real.pi * lam n * ε))) ≤ ε * (r / (1 - r)) :=
        mul_le_mul_of_nonneg_left hb hε.le
    _ ≤ 1 / (2 * Real.pi) := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by linarith only [hr1]) (by positivity)]
      nlinarith only [hc]

/-- For integer atom masses, a pole residue below `√2` forces the ordinary integer spectrum. -/
theorem integer_spectrum_of_residue_sq_lt_two {A : ℕ → ℕ} {lam : ℕ → ℝ}
    (hmono : StrictMono lam) (hlam0 : lam 0 = 1) (hA1 : ∀ n, 1 ≤ A n)
    (ha : Summable fun n => (A n : ℝ) / lam n ^ 2) {β : ℝ}
    (hsmall : (2 * β) ^ 2 < 2)
    {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * freqTheta (fun n => ((A n : ℝ) : ℂ)) lam x⁻¹ +
        -(β : ℂ) + (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x) :
    β = 1 / 2 ∧ ∀ n, lam n = n + 1 ∧ A n = 1 := by
  let a : ℕ → ℝ := fun n => A n
  have hlam : ∀ n, 1 ≤ lam n := fun n => hlam0 ▸ hmono.monotone (Nat.zero_le n)
  have hpos : ∀ n, 0 < lam n := fun n => lt_of_lt_of_le one_pos (hlam n)
  have ha0 : ∀ n, 0 ≤ a n := fun n => Nat.cast_nonneg _
  have ha1 : ∀ n, 1 ≤ a n := fun n => by
    dsimp only [a]
    exact_mod_cast hA1 n
  have haC : Summable fun n => ‖(a n : ℂ)‖ / lam n ^ 2 :=
    ha.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 n)]
  have hL := fun z hz => freqSeries_eq_of_theta_defect ha0 hlam ha hgm hgb hθ (z := z) hz
  have hC0 := tendsto_abelCos_zero_of_theta_defect ha0 hlam ha hgm hgb hgi hθ
  have hatom : ∀ m, Tendsto (abelCos a lam (lam m)) (𝓝[>] 0)
      (𝓝 (a m / (2 * Real.pi))) := by
    intro m
    obtain ⟨c, hc, hsep⟩ := exists_sep_of_strictMono hmono hpos m
    have hres := tendsto_mul_freqSeries_atom (a := fun n => (a n : ℂ)) hlam haC rfl
      (hpos m) hc hsep
    have hh := abel_limit_of_defective_series ha0 hlam ha hgm hgb hgi hL (hpos m) hres
    have hre : ((a m : ℂ) / (2 * Real.pi)).re = a m / (2 * Real.pi) := by
      rw [show ((a m : ℂ) / (2 * Real.pi)) = ((a m / (2 * Real.pi) : ℝ) : ℂ) by
        push_cast; ring, Complex.ofReal_re]
    rwa [hre] at hh
  have hmass : ∀ m, a m ≤ 2 * β := by
    intro m
    have hh : a m / (2 * Real.pi) ≤ β / Real.pi := by
      refine le_of_tendsto_of_tendsto (hatom m) hC0 ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact abelCos_le_of_le hlam ha0 ha hε fun n => by simpa using Real.cos_le_one _
    have hp := Real.pi_pos
    rw [div_le_div_iff₀ (by positivity) hp] at hh
    nlinarith only [hh, hp]
  have hρ1 : 1 ≤ 2 * β := (ha1 0).trans (hmass 0)
  have hρ2 : 2 * β < 2 := by nlinarith only [hsmall, hρ1]
  have hunitN : ∀ n, A n = 1 := by
    intro n
    have hh : (A n : ℝ) < 2 := (hmass n).trans_lt hρ2
    have hn : A n < 2 := by exact_mod_cast hh
    have hn1 := hA1 n
    omega
  have hunit : a = fun _ => 1 := funext fun n => by simp only [a, hunitN n, Nat.cast_one]
  have hsep : ∀ n, 1 ≤ lam (n + 1) - lam n := by
    intro n
    by_contra! hn
    let d : ℝ := lam (n + 1) - lam n
    have hd : 0 < d := sub_pos.mpr (hmono (Nat.lt_succ_self n))
    have hd1 : d < 1 := hn
    have hgap : Tendsto (abelCos a lam d) (𝓝[>] 0) (𝓝 0) := by
      have hdist : ∀ m, (1 - d) * lam m ≤ |lam m - d| := by
        intro m
        rw [abs_of_pos (by linarith only [hlam m, hd1])]
        nlinarith only [hlam m, hd.le]
      have hres := tendsto_mul_freqSeries_gap (a := fun n => (a n : ℂ)) hlam haC hd.le
        (by linarith only [hd1]) hdist
      simpa using abel_limit_of_defective_series ha0 hlam ha hgm hgb hgi hL hd hres
    have hleft := ((hatom n).add (hatom (n + 1))).const_mul (2 * (2 * β))
    have hright := (hC0.const_mul ((2 * β) ^ 2 + 2)).add (hgap.const_mul 2)
    have hh := le_of_tendsto_of_tendsto hleft hright (show ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        2 * (2 * β) * (abelCos a lam (lam n) ε + abelCos a lam (lam (n + 1)) ε) ≤
        ((2 * β) ^ 2 + 2) * abelCos a lam 0 ε + 2 * abelCos a lam d ε from by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact abelCos_three_point ha0 hlam ha (2 * β) (lam n) (lam (n + 1)) hε)
    simp only [a, hunitN, Nat.cast_one, mul_zero, add_zero] at hh
    have hh' : 2 * (2 * β) / Real.pi ≤ (((2 * β) ^ 2 + 2) * β) / Real.pi := by
      convert hh using 1 <;> ring
    rw [div_le_div_iff_of_pos_right Real.pi_pos] at hh'
    have hp : 0 < (2 * β) * (2 - (2 * β) ^ 2) :=
      mul_pos (lt_of_lt_of_le zero_lt_one hρ1) (sub_pos.mpr hsmall)
    nlinarith only [hh', hp]
  have hlower : ∀ n : ℕ, (n : ℝ) + 1 ≤ lam n := by
    intro n
    induction n with
    | zero => simp [hlam0]
    | succ n ih =>
      have hh := hsep n
      push_cast
      linarith only [hh, ih]
  have hb : β / Real.pi ≤ 1 / (2 * Real.pi) := by
    apply le_of_tendsto hC0
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hunit]
    exact abelCos_zero_le_of_nat_le hlower hε
  have hbhalf : β ≤ 1 / 2 := by
    have hp := Real.pi_pos
    rw [div_le_div_iff₀ hp (by positivity)] at hb
    nlinarith only [hb, hp]
  obtain ⟨hb, hvals⟩ := integer_spectrum_of_integrable_theta_defect hmono hlam0 ha1 ha hbhalf
    hgm hgb hgi hθ
  exact ⟨hb, fun n => ⟨(hvals n).1, hunitN n⟩⟩

end GaloisForLFunctions.ArithmeticPositiveDuality
