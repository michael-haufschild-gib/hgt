import GaloisForLFunctions.RHTower.HighExponentShellClockMeasure
import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.RHTower.Suzuki.SuzukiDiagonalResolventInstantiation
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PortRecurrenceJets
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.MarkedEulerShellSkeleton

/-!
# The marked Euler shell: Mellin–GNS realization, recurrence, and the normalization wall

The full positive shell measure at abscissa `σ > 1` is coefficient faithful, its logarithmic moments
are the derivatives of the analytic shell source, and every finite Hankel block of the GNS
correlations is strictly positive definite.  The observed dynamics is recurrent with compact
resolvent, while the unwrapped logarithmic history has divergent energy.

No finite positive normalization reaches the physical Mass half-density prime fibre: matching the
pure-power radial weights forces `mσ = 1`, hence `σ ≤ 1/12`, where the shell mass is infinite, and
the target Mass vector itself has divergent squared norm.
-/

namespace HTGeometry.ConstraintMotiveRelativity

open RHTower Filter Topology
open scoped LSeries.notation

section MellinGNS

/-- **`(ESG.16)`.**  The unnormalized shell measure is coefficient faithful. -/
theorem shellIndicator_eq_rpow_mul_shellMass (m : ℕ) (σ : ℝ) {n : ℕ} (hn : 0 < n) :
    (shellIndicator m n : ℝ) = (n : ℝ) ^ σ * shellMass m σ n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow : ((n : ℝ) ^ σ) ≠ 0 := (Real.rpow_pos_of_pos hn0 σ).ne'
  rw [shellMass]
  field_simp

/-- **`(ESG.16)`.**  The marked pair `(Z, P)` is coefficient faithful. -/
theorem shellIndicator_eq_shellMellin_mul_shellProbability {m : ℕ} (hm : m ≠ 0) {σ : ℝ}
    (hσ : 1 < σ) {n : ℕ} (hn : 0 < n) :
    (shellIndicator m n : ℝ) = shellMellin m σ * (n : ℝ) ^ σ * shellProbability m σ n := by
  have hZ : shellMellin m σ ≠ 0 := (shellMellin_pos hm hσ).ne'
  rw [shellProbability, shellIndicator_eq_rpow_mul_shellMass m σ hn]
  field_simp

theorem summable_shellMass_mul_log_pow (m k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => shellMass m σ n * (Real.log n) ^ k := by
  have hmaj : Summable (fun n : ℕ => |Real.log n| ^ k * (n : ℝ) ^ (-σ)) :=
    summable_abs_log_natCast_pow_mul_rpow_neg k σ hσ
  refine Summable.of_norm_bounded hmaj fun n => ?_
  have hInd : (shellIndicator m n : ℝ) ≤ 1 := by
    rcases shellIndicator_eq_zero_or_one m n with h | h <;> rw [h] <;> norm_num
  have hInd0 : (0 : ℝ) ≤ (shellIndicator m n : ℝ) := by
    rcases shellIndicator_eq_zero_or_one m n with h | h <;> rw [h] <;> norm_num
  have hpow : (0 : ℝ) ≤ (((n : ℝ)) ^ σ)⁻¹ := by positivity
  have hrw : |Real.log n| ^ k * (n : ℝ) ^ (-σ) = (((n : ℝ)) ^ σ)⁻¹ * |Real.log n| ^ k := by
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
    ring
  rw [Real.norm_eq_abs, abs_mul, shellMass, abs_mul, abs_of_nonneg hInd0, abs_of_nonneg hpow,
    abs_pow, hrw]
  have hA : (0 : ℝ) ≤ (((n : ℝ)) ^ σ)⁻¹ * |Real.log (n : ℝ)| ^ k := by positivity
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (shellIndicator m n : ℝ)) hA]

theorem summable_shellProbability_mul_log_pow (m k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => shellProbability m σ n * (Real.log n) ^ k := by
  have h := (summable_shellMass_mul_log_pow m k hσ).div_const (shellMellin m σ)
  refine h.congr fun n => ?_
  rw [shellProbability]
  ring

/-- **`(ESG.18)`.**  The GNS correlation `⟨D^iΩ, D^jΩ⟩`. -/
noncomputable def shellGNS (m : ℕ) (σ : ℝ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, shellProbability m σ n * (Real.log n) ^ k

theorem shellGNS_eq_shellLogMoment (m : ℕ) (σ : ℝ) (k : ℕ) :
    shellGNS m σ k = shellLogMoment m k σ := by
  rw [shellGNS, shellLogMoment, ← tsum_div_const]
  refine tsum_congr fun n => ?_
  rw [shellProbability, shellMass]
  ring

/-- **`(ESG.17)`.**  The unnormalized logarithmic moments are the shell source derivatives. -/
theorem ofReal_shellMassMoment {m : ℕ} (hm : m ≠ 0) (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    ((∑' n : ℕ, shellMass m σ n * (Real.log n) ^ k : ℝ) : ℂ)
      = (-1 : ℂ) ^ k * iteratedDeriv k (shellSource m) (σ : ℂ) := by
  have hZ : ((shellMellin m σ : ℝ) : ℂ) = shellSource m (σ : ℂ) := ofReal_shellMellin hm hσ
  have hZ0 : shellSource m (σ : ℂ) ≠ 0 := by
    rw [← hZ]
    exact_mod_cast (shellMellin_pos hm hσ).ne'
  have hnum : (∑' n : ℕ, shellMass m σ n * (Real.log n) ^ k)
      = shellLogMoment m k σ * shellMellin m σ := by
    rw [shellLogMoment, div_mul_cancel₀ _ (shellMellin_pos hm hσ).ne']
    exact tsum_congr fun n => by rw [shellMass]
  rw [hnum, Complex.ofReal_mul, ofReal_shellLogMoment hm k hσ, hZ]
  field_simp

/-- **`(ESG.18)`.**  Every GNS correlation is the corresponding normalized source derivative. -/
theorem ofReal_shellGNS {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) (i j : ℕ) :
    ((shellGNS m σ (i + j) : ℝ) : ℂ)
      = (-1 : ℂ) ^ (i + j) * iteratedDeriv (i + j) (shellSource m) (σ : ℂ)
        / shellSource m (σ : ℂ) := by
  rw [shellGNS_eq_shellLogMoment m σ, ofReal_shellLogMoment hm (i + j) hσ]

theorem shellProbability_prime_pow_pos {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) {σ : ℝ}
    (hσ : 1 < σ) : 0 < shellProbability m σ (p ^ m) := by
  have hpm : (0 : ℝ) < ((p ^ m : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos m
  have h2 : 0 < shellMellin m σ := shellMellin_pos hm hσ
  have hmass : shellMass m σ (p ^ m) = ((((p ^ m : ℕ) : ℝ)) ^ σ)⁻¹ := by
    rw [shellMass, shellIndicator_prime_pow hp m]
    norm_num
  rw [shellProbability, hmass]
  positivity

/-- **`(ESG.18)`.**  The GNS Hankel form is the weighted sum of squares of polynomial values at the
logarithmic atoms. -/
theorem shellGNS_quadratic (m : ℕ) {σ : ℝ} (hσ : 1 < σ) (R : ℕ)
    (c : Fin (R + 1) → ℝ) :
    ∑ i : Fin (R + 1), ∑ j : Fin (R + 1), c i * c j * shellGNS m σ ((i : ℕ) + (j : ℕ))
      = ∑' n : ℕ, shellProbability m σ n
          * (∑ i : Fin (R + 1), c i * (Real.log n) ^ (i : ℕ)) ^ 2 := by
  have hsum : ∀ i j : Fin (R + 1), Summable fun n : ℕ =>
      shellProbability m σ n * (c i * (Real.log n) ^ (i : ℕ))
        * (c j * (Real.log n) ^ (j : ℕ)) := by
    intro i j
    have h := (summable_shellProbability_mul_log_pow m ((i : ℕ) + (j : ℕ)) hσ).mul_left
      (c i * c j)
    refine h.congr fun n => ?_
    rw [pow_add]
    ring
  have hstep : ∀ i : Fin (R + 1),
      ∑ j : Fin (R + 1), c i * c j * shellGNS m σ ((i : ℕ) + (j : ℕ))
        = ∑' n : ℕ, ∑ j : Fin (R + 1), shellProbability m σ n
            * (c i * (Real.log n) ^ (i : ℕ)) * (c j * (Real.log n) ^ (j : ℕ)) := by
    intro i
    rw [Summable.tsum_finsetSum (fun j _ => hsum i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [shellGNS, ← (summable_shellProbability_mul_log_pow m ((i : ℕ) + (j : ℕ)) hσ).tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [pow_add]
    ring
  rw [Finset.sum_congr rfl fun i _ => hstep i,
    ← Summable.tsum_finsetSum (fun i _ => summable_sum fun j _ => hsum i j)]
  refine tsum_congr fun n => ?_
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- **`(ESG.18)`.**  Every finite Hankel block of the GNS correlations is strictly positive
definite: a nonzero polynomial cannot vanish at every logarithmic atom `log(p^m)`. -/
theorem shellGNS_hankel_posDef {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) (R : ℕ)
    (c : Fin (R + 1) → ℝ) (hc : ∃ i, c i ≠ 0) :
    0 < ∑ i : Fin (R + 1), ∑ j : Fin (R + 1), c i * c j * shellGNS m σ ((i : ℕ) + (j : ℕ)) := by
  classical
  rw [shellGNS_quadratic m hσ R c]
  set q : Polynomial ℝ := ∑ i : Fin (R + 1), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) with hq
  have hqeval : ∀ x : ℝ, q.eval x = ∑ i : Fin (R + 1), c i * x ^ (i : ℕ) := by
    intro x
    rw [hq, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl fun i _ => by simp
  have hqne : q ≠ 0 := by
    obtain ⟨i, hi⟩ := hc
    intro h0
    apply hi
    have hcoeff : q.coeff (i : ℕ) = c i := by
      rw [hq, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Fin.val_eq_val, Ne.symm hj]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [← hcoeff, h0, Polynomial.coeff_zero]
  have hroot : ∃ p : ℕ, p.Prime ∧ q.eval (Real.log ((p ^ m : ℕ) : ℝ)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hinj : Set.InjOn (fun p : ℕ => Real.log ((p ^ m : ℕ) : ℝ)) {p : ℕ | p.Prime} := by
      intro a ha b hb hab
      have hapos : (0 : ℝ) < ((a ^ m : ℕ) : ℝ) := by exact_mod_cast pow_pos (ha : a.Prime).pos m
      have hbpos : (0 : ℝ) < ((b ^ m : ℕ) : ℝ) := by exact_mod_cast pow_pos (hb : b.Prime).pos m
      have h1 := Real.log_injOn_pos (Set.mem_Ioi.mpr hapos) (Set.mem_Ioi.mpr hbpos) hab
      have h2 : a ^ m = b ^ m := by exact_mod_cast h1
      exact Nat.pow_left_injective hm h2
    have hsub : (fun p : ℕ => Real.log ((p ^ m : ℕ) : ℝ)) '' {p : ℕ | p.Prime}
        ⊆ {x : ℝ | q.IsRoot x} := by
      rintro x ⟨p, hp, rfl⟩
      exact hcon p hp
    have hinf : ((fun p : ℕ => Real.log ((p ^ m : ℕ) : ℝ)) '' {p : ℕ | p.Prime}).Infinite :=
      Nat.infinite_setOf_prime.image hinj
    exact hqne (Polynomial.eq_zero_of_infinite_isRoot q (hinf.mono hsub))
  obtain ⟨p, hp, hpne⟩ := hroot
  have hsum2 : ∀ i j : Fin (R + 1), Summable fun n : ℕ =>
      shellProbability m σ n * (c i * (Real.log n) ^ (i : ℕ))
        * (c j * (Real.log n) ^ (j : ℕ)) := by
    intro i j
    have h := (summable_shellProbability_mul_log_pow m ((i : ℕ) + (j : ℕ)) hσ).mul_left
      (c i * c j)
    refine h.congr fun n => ?_
    rw [pow_add]
    ring
  have hsq : Summable fun n : ℕ => shellProbability m σ n
      * (∑ i : Fin (R + 1), c i * (Real.log n) ^ (i : ℕ)) ^ 2 := by
    have h1 : Summable fun n : ℕ => ∑ i : Fin (R + 1), ∑ j : Fin (R + 1),
        shellProbability m σ n * (c i * (Real.log n) ^ (i : ℕ))
          * (c j * (Real.log n) ^ (j : ℕ)) :=
      summable_sum fun i _ => summable_sum fun j _ => hsum2 i j
    refine h1.congr fun n => ?_
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  refine Summable.tsum_pos hsq (fun n => mul_nonneg (shellProbability_nonneg hm hσ n)
    (sq_nonneg _)) (p ^ m) ?_
  · have h1 : 0 < shellProbability m σ (p ^ m) := shellProbability_prime_pow_pos hp hm hσ
    have h2 : (∑ i : Fin (R + 1), c i * (Real.log ((p ^ m : ℕ) : ℝ)) ^ (i : ℕ)) ≠ 0 := by
      rw [← hqeval]
      exact hpne
    exact mul_pos h1 (by positivity)

/-- **`(ESG.19)`.**  The GNS phase correlation is the normalized shell source on the shifted
line. -/
theorem shellCharacteristic {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ∑' n : ℕ, (shellProbability m σ n : ℂ) * ((n : ℂ) ^ (-((t : ℂ) * Complex.I)))
      = shellSource m ((σ : ℂ) + (t : ℂ) * Complex.I) / shellSource m (σ : ℂ) := by
  have hs : 1 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]
    linarith
  have hterm : ∀ n : ℕ, LSeries.term ↗(shellIndicator m) ((σ : ℂ) + (t : ℂ) * Complex.I) n
      = (shellMass m σ n : ℂ) * ((n : ℂ) ^ (-((t : ℂ) * Complex.I))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, shellMass]
    · have hn0 : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      rw [LSeries.term_of_ne_zero hn.ne', Complex.cpow_add _ _ hn0, Complex.cpow_neg, shellMass]
      have hrp : ((((n : ℝ)) ^ σ : ℝ) : ℂ) = (n : ℂ) ^ ((σ : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n) σ, Complex.ofReal_natCast]
      have hne : ((n : ℂ) ^ ((σ : ℝ) : ℂ)) ≠ 0 := by
        rw [← hrp]
        exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast hn) σ).ne'
      have hne2 : ((n : ℂ) ^ (((t : ℂ) * Complex.I))) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn0)
      push_cast
      rw [hrp]
      field_simp
  have hLS : LSeries ↗(shellIndicator m) ((σ : ℂ) + (t : ℂ) * Complex.I)
      = shellSource m ((σ : ℂ) + (t : ℂ) * Complex.I) := LSeries_shellIndicator hm hs
  have hZ : ((shellMellin m σ : ℝ) : ℂ) = shellSource m (σ : ℂ) := ofReal_shellMellin hm hσ
  have hZ0 : shellSource m (σ : ℂ) ≠ 0 := by
    rw [← hZ]; exact_mod_cast (shellMellin_pos hm hσ).ne'
  rw [← hLS, LSeries, tsum_congr hterm, ← hZ]
  rw [eq_div_iff (by rw [hZ]; exact hZ0), ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  have hZc : ((shellMellin m σ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (shellMellin_pos hm hσ).ne'
  rw [shellProbability]
  push_cast
  field_simp

end MellinGNS

/-! ### Compact-resolvent recurrence with open lifted history -/

section Recurrence

/-- The GNS coordinate vector of the marked shell state. -/
noncomputable def shellVec (m : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt (shellProbability m σ n) : ℂ)

theorem summable_normSq_shellVec {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => ‖shellVec m σ n‖ ^ 2 := by
  refine (hasSum_shellProbability hm hσ).summable.congr fun n => ?_
  rw [shellVec, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (shellProbability_nonneg hm hσ n)]

/-- **`(ESG.15)`.**  The observed shell orbit `U_t Ω` in the canonical coordinate model. -/
noncomputable def shellOrbit {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) : ℝ → SourceL2 ℕ :=
  portOrbit (fun n : ℕ => Real.log n) (shellVec m σ) (summable_normSq_shellVec hm hσ)

/-- **§5.**  The observed orbit has compact norm closure. -/
theorem isCompact_closure_shellOrbit {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    IsCompact (closure (Set.range (shellOrbit hm hσ))) :=
  isCompact_closure_range_portOrbit

/-- **§5.**  The observed orbit returns arbitrarily close to its start at arbitrarily late times. -/
theorem shellOrbit_recurrent {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) {ε : ℝ} (hε : 0 < ε)
    (T : ℝ) : ∃ t : ℝ, T < t ∧ ‖shellOrbit hm hσ t - shellOrbit hm hσ 0‖ < ε :=
  portOrbit_recurrent hε T

/-- **`(ESG.21)`.**  The second logarithmic moment of the shell state is strictly positive. -/
theorem shellGNS_two_pos {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) : 0 < shellGNS m σ 2 := by
  refine Summable.tsum_pos (summable_shellProbability_mul_log_pow m 2 hσ)
    (fun n => mul_nonneg (shellProbability_nonneg hm hσ n) (sq_nonneg _)) (2 ^ m) ?_
  have h1 : 0 < shellProbability m σ (2 ^ m) := shellProbability_prime_pow_pos Nat.prime_two hm hσ
  have h2 : (0 : ℝ) < Real.log ((2 ^ m : ℕ) : ℝ) := by
    have hlt : (1 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by
      have : 1 < 2 ^ m := Nat.one_lt_two_pow hm
      exact_mod_cast this
    exact Real.log_pos hlt
  exact mul_pos h1 (by positivity)

/-- **`(ESG.20)`, `(ESG.21)`.**  The unwrapped logarithmic history has energy `t²·μ₂`. -/
theorem shellHistoryEnergy {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    (∑' n : ℕ, (-t * Real.log n * Real.sqrt (shellProbability m σ n)) ^ 2)
      = t ^ 2 * shellGNS m σ 2 := by
  rw [shellGNS, ← (summable_shellProbability_mul_log_pow m 2 hσ).tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (shellProbability_nonneg hm hσ n)]
  ring

/-- **`(ESG.21)`.**  The lifted history energy diverges. -/
theorem tendsto_shellHistoryEnergy {m : ℕ} (hm : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun t : ℝ => t ^ 2 * shellGNS m σ 2) atTop atTop :=
  Filter.Tendsto.atTop_mul_const (shellGNS_two_pos hm hσ) (tendsto_pow_atTop two_ne_zero)

/-- The diagonal resolvent entries of the logarithmic clock are uniformly bounded. -/
theorem norm_shellResolvent_le (n : ℕ) : ‖((Real.log n : ℂ) + Complex.I)⁻¹‖ ≤ 1 := by
  have h1 : (Real.log n : ℝ) ≤ ‖((Real.log n : ℂ) + Complex.I)‖ := by
    have h := Complex.abs_re_le_norm ((Real.log n : ℂ) + Complex.I)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero] at h
    exact le_trans (le_abs_self _) h
  have h2 : (1 : ℝ) ≤ ‖((Real.log n : ℂ) + Complex.I)‖ := by
    have hsq : ‖((Real.log n : ℂ) + Complex.I)‖ ^ 2 = (Real.log n) ^ 2 + 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero, Complex.add_im,
        Complex.ofReal_im, Complex.I_im, zero_add]
      ring
    nlinarith [norm_nonneg ((Real.log n : ℂ) + Complex.I), sq_nonneg (Real.log (n : ℝ))]
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ h2

theorem tendsto_norm_shellResolvent :
    Tendsto (fun n : ℕ => ‖((Real.log n : ℂ) + Complex.I)⁻¹‖) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (Real.log n)⁻¹) atTop (nhds 0) := hlog.inv_tendsto_atTop
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hinv
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  have h1 : (Real.log n : ℝ) ≤ ‖((Real.log n : ℂ) + Complex.I)‖ := by
    have h := Complex.abs_re_le_norm ((Real.log n : ℂ) + Complex.I)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero] at h
    exact le_trans (le_abs_self _) h
  rw [norm_inv]
  exact inv_anti₀ hn h1

/-- **§5.**  The logarithmic clock has compact resolvent: its diagonal resolvent entries tend to
zero. -/
theorem isCompactOperator_shellResolvent :
    IsCompactOperator (diagonalOperator (fun n : ℕ => ((Real.log n : ℂ) + Complex.I)⁻¹)
      norm_shellResolvent_le) :=
  GaloisForLFunctions.RHTower.isCompactOperator_diagonalOperator _ norm_shellResolvent_le
    tendsto_norm_shellResolvent

end Recurrence

/-! ### The normalization wall -/

section Wall

/-- **`(ESG.23)`.**  The shell multiplier at the critical clock point is a positive real. -/
theorem shell_pole_residue_pos {m : ℕ} (hm : 2 ≤ m) :
    ∃ r : ℝ, 0 < r ∧ shellMultiplier m 1 = (r : ℂ) := shellMultiplier_one_eq_ofReal_pos hm

/-- **`(ESG.24)`.**  Matching the pure-power radial weights of the shell state to the Mass
half-density weights up to one finite global normalization forces `mσ = 1`. -/
theorem normalization_forces_one {m : ℕ} {σ lam : ℝ}
    (h : ∀ p : ℕ, p.Prime → ((p : ℝ) ^ (-((m : ℝ) * σ) / 2))
      = lam * ((p : ℝ) ^ (-(1 : ℝ) / 2))) :
    (m : ℝ) * σ = 1 := by
  have h2 := h 2 Nat.prime_two
  have h3 := h 3 Nat.prime_three
  push_cast at h2 h3
  have hp2 : (0 : ℝ) < 2 := by norm_num
  have hp3 : (0 : ℝ) < 3 := by norm_num
  have hr2 : (0 : ℝ) < (2 : ℝ) ^ (-((m : ℝ) * σ) / 2) := Real.rpow_pos_of_pos hp2 _
  have hs2 : (0 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hp2 _
  have hs3 : (0 : ℝ) < (3 : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hp3 _
  have hlam : 0 < lam := by
    rcases lt_trichotomy lam 0 with hl | hl | hl
    · nlinarith [h2, hr2, hs2]
    · rw [hl, zero_mul] at h2; linarith
    · exact hl
  have hlog2 := congrArg Real.log h2
  have hlog3 := congrArg Real.log h3
  rw [Real.log_rpow hp2, Real.log_mul hlam.ne' hs2.ne', Real.log_rpow hp2] at hlog2
  rw [Real.log_rpow hp3, Real.log_mul hlam.ne' hs3.ne', Real.log_rpow hp3] at hlog3
  have hne : Real.log 2 ≠ Real.log 3 := by
    intro hcon
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr hp2) (Set.mem_Ioi.mpr hp3) hcon
    norm_num at this
  have hdiff : (-((m : ℝ) * σ) / 2) * (Real.log 2 - Real.log 3)
      = (-(1 : ℝ) / 2) * (Real.log 2 - Real.log 3) := by
    rw [mul_sub, mul_sub]
    linarith [hlog2, hlog3]
  have hsub : Real.log 2 - Real.log 3 ≠ 0 := sub_ne_zero.mpr hne
  have := mul_right_cancel₀ hsub hdiff
  linarith

/-- **`(ESG.24)`.**  For `m ≥ 12` the matched abscissa lies outside the convergence half-plane of
the shell measure. -/
theorem normalization_wall {m : ℕ} (hm : 12 ≤ m) {σ lam : ℝ}
    (h : ∀ p : ℕ, p.Prime → ((p : ℝ) ^ (-((m : ℝ) * σ) / 2))
      = lam * ((p : ℝ) ^ (-(1 : ℝ) / 2))) :
    ¬ (1 < σ) := by
  have hmσ := normalization_forces_one h
  have hm0 : (12 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  intro hσ
  nlinarith [hmσ, hm0, hσ]

/-- **`(ESG.25)`.**  The target Mass half-density vector has divergent squared norm. -/
theorem not_summable_massCoeff_sq :
    ¬ Summable fun p : Nat.Primes => (massCoeff (p : ℕ)) ^ 2 := by
  intro hsum
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hle : ∀ p : Nat.Primes,
      (Real.log 2) ^ 2 * (1 / ((p : ℕ) : ℝ)) ≤ (massCoeff (p : ℕ)) ^ 2 := by
    intro p
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    have hlogle : Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_le_log (by norm_num) hp2
    have hsq : Real.sqrt ((p : ℕ) : ℝ) ^ 2 = ((p : ℕ) : ℝ) := Real.sq_sqrt hppos.le
    rw [massCoeff, div_pow, hsq, one_div, div_eq_mul_inv]
    have hnum : (Real.log 2) ^ 2 ≤ (Real.log ((p : ℕ) : ℝ)) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hppos.le)
  have hcomp : Summable fun p : Nat.Primes => (Real.log 2) ^ 2 * (1 / ((p : ℕ) : ℝ)) :=
    hsum.of_nonneg_of_le (fun p => by positivity) hle
  have hone : Summable fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ) := by
    have := hcomp.mul_left ((Real.log 2) ^ 2)⁻¹
    refine this.congr fun p => ?_
    field_simp
  exact Nat.Primes.not_summable_one_div hone

end Wall

/-! ### Sharp reporter nonfaithfulness -/

section Mixed

/-- **§8.**  A perturbation of the shell source at one mixed-shell atom. -/
noncomputable def mixedPerturb (m : ℕ) (b : ℝ) (n : ℕ) : ℝ :=
  if n = 2 ^ m * 3 then b else (shellIndicator m n : ℝ)

theorem prime_pow_ne_mixedAtom {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) :
    p ^ m ≠ 2 ^ m * 3 := by
  intro heq
  have h2 : (2 : ℕ) ∣ p ^ m := by
    rw [heq]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 hm) 3
  have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)).symm
  subst hp2
  have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
  omega

/-- **§8.**  The mixed perturbation is invisible to the pure-power reporters. -/
theorem mixedPerturb_prime_pow {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≠ 0) (b : ℝ) :
    mixedPerturb m b (p ^ m) = 1 := by
  rw [mixedPerturb, if_neg (prime_pow_ne_mixedAtom hp hm), shellIndicator_prime_pow hp m]
  norm_num

theorem summable_mixedPerturb_sub (m : ℕ) (b : ℝ) (σ : ℝ) :
    Summable fun n : ℕ => mixedPerturb m b n * (((n : ℝ)) ^ σ)⁻¹ - shellMass m σ n := by
  classical
  refine summable_of_ne_finset_zero (s := {2 ^ m * 3}) fun n hn => ?_
  have hne : n ≠ 2 ^ m * 3 := by simpa using hn
  rw [mixedPerturb, if_neg hne, shellMass, sub_self]

theorem summable_mixedPerturb (m : ℕ) (b : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => mixedPerturb m b n * (((n : ℝ)) ^ σ)⁻¹ := by
  have h := (summable_mixedPerturb_sub m b σ).add (summable_shellMass m hσ)
  refine h.congr fun n => ?_
  ring

/-- **§8.**  The mixed perturbation changes the unnormalized shell measure by exactly one atom. -/
theorem tsum_mixedPerturb_sub (m : ℕ) (b : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, mixedPerturb m b n * (((n : ℝ)) ^ σ)⁻¹) - ∑' n : ℕ, shellMass m σ n
      = (b - (shellIndicator m (2 ^ m * 3) : ℝ)) * ((((2 ^ m * 3 : ℕ) : ℝ)) ^ σ)⁻¹ := by
  classical
  rw [← (summable_mixedPerturb m b hσ).tsum_sub (summable_shellMass m hσ)]
  rw [tsum_eq_single (2 ^ m * 3) (fun n hn => ?_)]
  · rw [mixedPerturb, if_pos rfl, shellMass]
    push_cast
    ring
  · rw [mixedPerturb, if_neg hn, shellMass, sub_self]

/-- **§8.**  A nontrivial mixed perturbation is detected by the unnormalized measure. -/
theorem tsum_mixedPerturb_ne (m : ℕ) {b : ℝ} {σ : ℝ} (hσ : 1 < σ)
    (hb : b ≠ (shellIndicator m (2 ^ m * 3) : ℝ)) :
    (∑' n : ℕ, mixedPerturb m b n * (((n : ℝ)) ^ σ)⁻¹) ≠ ∑' n : ℕ, shellMass m σ n := by
  intro heq
  have hz := tsum_mixedPerturb_sub m b hσ
  rw [heq, sub_self] at hz
  have hpos : (0 : ℝ) < ((((2 ^ m * 3 : ℕ) : ℝ)) ^ σ)⁻¹ := by
    have : (0 : ℝ) < ((2 ^ m * 3 : ℕ) : ℝ) := by positivity
    positivity
  exact hb (by
    have := (mul_eq_zero.mp hz.symm).resolve_right hpos.ne'
    linarith [sub_eq_zero.mp this])

end Mixed

end HTGeometry.ConstraintMotiveRelativity
