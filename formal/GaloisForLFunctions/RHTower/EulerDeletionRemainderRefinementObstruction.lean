import GaloisForLFunctions.RHTower.EulerDeletionRemainderMobiusInversion

/-!
# Nonvanishing of the retained remainder refinement

The actual modulus remainder decays with an explicit power bound. For a decaying
sequence, an exact dilation identity with a noncontracting multiplier forces every
positive-index value to vanish. Arithmetic reconstruction excludes this conclusion
at every zeta zero with real part in `(0, 1]` and exponent different from one.

Consequently, for each fixed nontrivial modulus, some remainder refinement is
nonzero. This excludes the specified scalar vanishing law, not other arithmetic
constraints or a classification of zeros.
-/

noncomputable section
open scoped BigOperators
open Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- Uniform decay bound for the actual modulus remainder, with a finite explicit constant. -/
theorem norm_infiniteRemainder_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {m : ℕ} (hm : 0 < m) :
    ‖infiniteRemainder s m‖ ≤
      ((‖s * (s + 1)‖ / (s.re + 1)) *
        ∑' n : ℕ+, (n : ℝ) ^ (-2 * s.re - 1)) * (m : ℝ) ^ (-2 * s.re) := by
  let a : ℝ := -2 * s.re - 1
  let C : ℝ := ‖s * (s + 1)‖ / (s.re + 1)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : Summable (fun n : ℕ+ => (n : ℝ) ^ a) :=
    (Real.summable_nat_rpow.2 (by dsimp [a]; linarith)).subtype _
  have hh : Summable (fun n : ℕ+ => ‖weightedPowerRemainder s (m * n)‖) := by
    simpa only [PNat.val_ofNat, Nat.one_mul] using
      (summable_norm_weightedPowerRemainder_pair hs hs1 hm).prod_factor (1 : ℕ+)
  have hb : ‖infiniteRemainder s m / (m : ℂ)‖ ≤
      C * (m : ℝ) ^ a * ∑' n : ℕ+, (n : ℝ) ^ a := by
    rw [infiniteRemainder_div_eq_multiples s hm]
    refine (norm_tsum_le_tsum_norm hh).trans ?_
    rw [← tsum_mul_left]
    apply hh.tsum_le_tsum ?_ (ha.mul_left (C * (m : ℝ) ^ a))
    intro n
    refine (norm_weightedPowerRemainder_le hs hs1 (Nat.mul_pos hm n.pos)).trans_eq ?_
    simp only [Nat.cast_mul]
    change C * ((m : ℝ) * (n : ℝ)) ^ a = _
    rw [Real.mul_rpow hm'.le (by positivity)]
    ring
  rw [norm_div, Complex.norm_natCast] at hb
  have he : ((C * (m : ℝ) ^ a) * ∑' n : ℕ+, (n : ℝ) ^ a) * m =
      (C * ∑' n : ℕ+, (n : ℝ) ^ a) * (m : ℝ) ^ (-2 * s.re) := by
    calc
      _ = (C * ∑' n : ℕ+, (n : ℝ) ^ a) * ((m : ℝ) ^ a * (m : ℝ) ^ (1 : ℝ)) := by
        rw [Real.rpow_one]
        ring
      _ = _ := by rw [← Real.rpow_add hm']; congr 2; dsimp [a]; ring
  exact ((div_le_iff₀ hm').1 hb).trans_eq he

/-- The complete retained remainder tends to zero as the integer modulus grows. -/
theorem tendsto_infiniteRemainder {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (infiniteRemainder s) atTop (𝓝 0) := by
  have hlim := (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * s.re)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have he : -(2 * s.re) = -2 * s.re := by ring
  have hlim' := hlim.const_mul ((‖s * (s + 1)‖ / (s.re + 1)) *
    ∑' n : ℕ+, (n : ℝ) ^ (-2 * s.re - 1))
  simp only [Function.comp_apply, he, mul_zero] at hlim'
  apply squeeze_zero_norm' ?_ hlim'
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact norm_infiniteRemainder_le hs hs1 (by omega)

/-- A decaying sequence cannot have a noncontracting exact dilation law unless it is zero. -/
theorem eq_zero_of_decaying_refinement {f : ℕ → ℂ} {A : ℂ} {p : ℕ}
    (hp : 1 < p) (hA : 1 ≤ ‖A‖) (hf : Tendsto f atTop (𝓝 0))
    (hc : ∀ q : ℕ, 0 < q → f (p * q) - f p - A * f q + A * f 1 = 0) :
    ∀ q : ℕ, 0 < q → f q = 0 := by
  have hd : Tendsto (fun q : ℕ => p * q) atTop atTop :=
    tendsto_atTop_mono (fun q => by change q ≤ p * q; nlinarith) tendsto_id
  have hl := (((hf.comp hd).sub_const (f p)).sub (hf.const_mul A)).add_const (A * f 1)
  have hl0 : Tendsto (fun q => f (p * q) - f p - A * f q + A * f 1) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with q hq
    exact (hc q (by omega)).symm
  have hbase : f p = A * f 1 := by
    have he := tendsto_nhds_unique hl hl0
    simpa only [mul_zero, sub_zero, zero_sub, neg_add_eq_zero] using he
  have hscale (q : ℕ) (hq : 0 < q) : f (p * q) = A * f q := by
    have h := hc q hq
    rw [hbase] at h
    linear_combination h
  intro q hq
  have hiter (n : ℕ) : f (p ^ n * q) = A ^ n * f q := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Nat.mul_assoc, hscale _ (Nat.mul_pos (pow_pos (by omega) n) hq), ih, pow_succ']
      ring
  have ht : Tendsto (fun n : ℕ => p ^ n * q) atTop atTop :=
    tendsto_atTop_mono (fun n => by nlinarith [Nat.zero_le (p ^ n)])
      (tendsto_pow_atTop_atTop_of_one_lt hp)
  have hn : ‖f q‖ ≤ 0 := by
    apply ge_of_tendsto (by simpa only [norm_zero] using (hf.comp ht).norm)
    apply Eventually.of_forall
    intro n
    simp only [Function.comp_apply]
    rw [hiter, norm_mul, norm_pow]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hA)
  exact norm_eq_zero.1 (le_antisymm hn (norm_nonneg _))

/-- For real part at most one, the quadratic dilation multiplier is noncontracting. -/
theorem one_le_norm_quadraticPower {s : ℂ} (hs : s.re ≤ 1) {p : ℕ} (hp : 1 ≤ p) :
    1 ≤ ‖quadraticPower s p‖ := by
  rw [quadraticPower, Complex.norm_natCast_cpow_of_pos (by omega), diagonalExponent_eq]
  apply Real.one_le_rpow (by exact_mod_cast hp)
  simp only [Complex.sub_re, Complex.ofReal_re]
  norm_num
  linarith

/-- At every zero, some corrected refinement survives for each nontrivial fixed modulus. -/
theorem exists_remainder_refinement_ne_zero_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    {p : ℕ} (hp : 1 < p) :
    ∃ q : ℕ, 0 < q ∧
      infiniteRemainder s (p * q) - infiniteRemainder s p -
        quadraticPower s p * infiniteRemainder s q +
        quadraticPower s p * infiniteRemainder s 1 ≠ 0 := by
  by_contra h
  push Not at h
  have hzero := eq_zero_of_decaying_refinement hp
    (one_le_norm_quadraticPower hs' (by omega)) (tendsto_infiniteRemainder hs hs1) h
  obtain ⟨q, hq⟩ := exists_infiniteRemainder_ne_zero_at_zero hs hs1 hz
  exact hq (hzero q q.pos)

end RHTower.DeletionMixedRefinement
