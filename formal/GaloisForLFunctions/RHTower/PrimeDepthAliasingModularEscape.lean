import GaloisForLFunctions.RHTower.TwoPrimeKummerClockSeparation
import GaloisForLFunctions.RHTower.PrimeBurnolThetaModularHolonomy
import GaloisForLFunctions.HTGeometry.TwoSiteModularHolonomyEscape

/-!
# Prime-depth aliasing and modular escape

Fixed distinct primes admit positive depths whose archimedean Burnol rates are arbitrarily close.
Their normalized cubic-Cauchy Gram capacity is consequently unbounded before any divisor is
supplied. Combined with the two-site modular block law, this is the scalar source of cofinal
source-frame holonomy escape.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem log_two_le_kummerFreq_of_coordinates_nonneg
    (z : ℤ × ℤ) (hz : z ≠ (0, 0)) (h1 : 0 ≤ z.1) (h2 : 0 ≤ z.2) :
    Real.log 2 ≤ kummerFreq z := by
  have hL3pos : 0 < Real.log 3 := lt_of_lt_of_le log_two_pos log_two_lt_log_three
  rcases eq_or_lt_of_le h1 with h10 | h1pos
  · have h2pos : 1 ≤ z.2 := by
      rcases eq_or_lt_of_le h2 with h20 | h2pos
      · exact absurd (Prod.ext h10.symm h20.symm) hz
      · omega
    have h2R : (1 : ℝ) ≤ (z.2 : ℝ) := by exact_mod_cast h2pos
    rw [kummerFreq, ← h10]
    have hm : Real.log 2 ≤ (z.2 : ℝ) * Real.log 3 := by
      calc
        Real.log 2 ≤ Real.log 3 := log_two_lt_log_three
        _ = 1 * Real.log 3 := (one_mul _).symm
        _ ≤ (z.2 : ℝ) * Real.log 3 :=
          mul_le_mul_of_nonneg_right h2R hL3pos.le
    simpa using hm
  · have h1R : (1 : ℝ) ≤ (z.1 : ℝ) := by exact_mod_cast h1pos
    rw [kummerFreq]
    have ha : Real.log 2 ≤ (z.1 : ℝ) * Real.log 2 := by
      calc
        Real.log 2 = 1 * Real.log 2 := (one_mul _).symm
        _ ≤ (z.1 : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right h1R log_two_pos.le
    have hb : 0 ≤ (z.2 : ℝ) * Real.log 3 :=
      mul_nonneg (by exact_mod_cast h2) hL3pos.le
    linarith

theorem log_two_le_abs_kummerFreq_of_mul_nonneg
    (z : ℤ × ℤ) (hz : z ≠ (0, 0)) (hsign : 0 ≤ z.1 * z.2) :
    Real.log 2 ≤ |kummerFreq z| := by
  rcases Int.mul_nonneg_iff.mp hsign with h | h
  · rcases h with ⟨h1, h2⟩
    have hfreq := log_two_le_kummerFreq_of_coordinates_nonneg z hz h1 h2
    rw [abs_of_nonneg (le_trans log_two_pos.le hfreq)]
    exact hfreq
  · rcases h with ⟨h1, h2⟩
    have hzneg : (-z.1, -z.2) ≠ (0, 0) := by
      intro hc
      apply hz
      have hc1 := congrArg Prod.fst hc
      have hc2 := congrArg Prod.snd hc
      simp only at hc1 hc2
      exact Prod.ext (by omega) (by omega)
    have hrec := log_two_le_kummerFreq_of_coordinates_nonneg
      (-z.1, -z.2) hzneg (by omega) (by omega)
    have hfreqneg : kummerFreq (-z.1, -z.2) = -kummerFreq z := by
      simp [kummerFreq]
      ring
    rw [hfreqneg] at hrec
    rw [abs_of_nonpos (by linarith [log_two_pos])]
    linarith

/-- Positive depths of fixed primes 2 and 3 have arbitrarily close, unequal Burnol rates. -/
theorem exists_two_three_positive_depth_collision {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      0 < |(m : ℝ) * Real.log 2 - (n : ℝ) * Real.log 3| ∧
      |(m : ℝ) * Real.log 2 - (n : ℝ) * Real.log 3| < epsilon := by
  let delta := min epsilon (Real.log 2)
  have hdelta : 0 < delta := lt_min hepsilon log_two_pos
  obtain ⟨z, hz, hpos, hsmall⟩ := exists_small_kummerFreq hdelta
  have hltlog : |kummerFreq z| < Real.log 2 :=
    lt_of_lt_of_le hsmall (min_le_right _ _)
  have hsign : z.1 * z.2 < 0 := by
    by_contra hnot
    have hnonneg : 0 ≤ z.1 * z.2 := le_of_not_gt hnot
    exact (not_lt_of_ge (log_two_le_abs_kummerFreq_of_mul_nonneg z hz hnonneg)) hltlog
  have heps : |kummerFreq z| < epsilon :=
    lt_of_lt_of_le hsmall (min_le_left _ _)
  rcases Int.mul_neg_iff.mp hsign with h | h
  · rcases h with ⟨h1, h2⟩
    let m := z.1.toNat
    let n := (-z.2).toNat
    have hm : 0 < m := by omega
    have hn : 0 < n := by omega
    have hmcast : (m : ℝ) = (z.1 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h1.le
    have hncast : (n : ℝ) = -(z.2 : ℝ) := by
      have hz2 : ((n : ℕ) : ℤ) = -z.2 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast hz2
    refine ⟨m, n, hm, hn, ?_, ?_⟩
    · have heq : (m : ℝ) * Real.log 2 - (n : ℝ) * Real.log 3 = kummerFreq z := by
        rw [hmcast, hncast, kummerFreq]
        ring
      rw [heq]
      exact hpos
    · have heq : (m : ℝ) * Real.log 2 - (n : ℝ) * Real.log 3 = kummerFreq z := by
        rw [hmcast, hncast, kummerFreq]
        ring
      rw [heq]
      exact heps
  · rcases h with ⟨h1, h2⟩
    let m := (-z.1).toNat
    let n := z.2.toNat
    have hm : 0 < m := by omega
    have hn : 0 < n := by omega
    have hmcast : (m : ℝ) = -(z.1 : ℝ) := by
      have hz1 : ((m : ℕ) : ℤ) = -z.1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast hz1
    have hncast : (n : ℝ) = (z.2 : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h2.le
    refine ⟨m, n, hm, hn, ?_, ?_⟩
    · have heq : (m : ℝ) * Real.log 2 - (n : ℝ) * Real.log 3 = -kummerFreq z := by
        rw [hmcast, hncast, kummerFreq]
        ring
      rw [heq, abs_neg]
      exact hpos
    · have heq : (m : ℝ) * Real.log 2 - (n : ℝ) * Real.log 3 = -kummerFreq z := by
        rw [hmcast, hncast, kummerFreq]
        ring
      rw [heq, abs_neg]
      exact heps

/-- Amplitude-free cubic-Cauchy capacity of one positive 2/3 prime-depth pair. -/
def twoThreePrimeDepthCubicCauchyCapacity (m n : ℕ) : ℝ :=
  64 * ((m : ℝ) * Real.log 2) ^ 3 * ((n : ℝ) * Real.log 3) ^ 3 /
    ((((m : ℝ) * Real.log 2) + ((n : ℝ) * Real.log 3)) ^ 6 -
      64 * ((m : ℝ) * Real.log 2) ^ 3 * ((n : ℝ) * Real.log 3) ^ 3)

/-- Literal 2/3 prime-depth cubic-Cauchy Gram capacities exceed every prescribed bound. -/
theorem exists_two_three_primeDepth_cubicCauchyCapacity_gt
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      M < twoThreePrimeDepthCubicCauchyCapacity m n := by
  let epsilon := Real.log 2 / (4 * (M + 1))
  have hM1 : 0 < M + 1 := by linarith
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  obtain ⟨m, n, hm, hn, hdiffpos, hdiffsmall⟩ :=
    exists_two_three_positive_depth_collision hepsilon
  let x := (m : ℝ) * Real.log 2
  let y := (n : ℝ) * Real.log 3
  let u := |x - y| / (x + y)
  change 0 < |x - y| at hdiffpos
  change |x - y| < epsilon at hdiffsmall
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < x := mul_pos (by exact_mod_cast hm) log_two_pos
  have hlog3 : 0 < Real.log 3 := lt_of_lt_of_le log_two_pos log_two_lt_log_three
  have hy : 0 < y := mul_pos (by exact_mod_cast hn) hlog3
  have hsum : 0 < x + y := add_pos hx hy
  have hsumlower : 2 * Real.log 2 ≤ x + y := by
    dsimp [x, y]
    have hxlow : Real.log 2 ≤ (m : ℝ) * Real.log 2 := by nlinarith
    have hylow : Real.log 2 ≤ (n : ℝ) * Real.log 3 := by
      have : Real.log 3 ≤ (n : ℝ) * Real.log 3 := by nlinarith
      exact log_two_lt_log_three.trans this
    linarith
  have hxy : x ≠ y := by
    intro h
    simp [h] at hdiffpos
  have hu : 0 < u := div_pos hdiffpos hsum
  have htarget : epsilon ≤ (1 / (8 * (M + 1))) * (x + y) := by
    dsimp [epsilon]
    rw [div_le_iff₀ (by positivity : 0 < 4 * (M + 1))]
    field_simp [hM1.ne']
    nlinarith
  have husmall : u < 1 / (8 * (M + 1)) := by
    change |x - y| / (x + y) < 1 / (8 * (M + 1))
    rw [div_lt_iff₀ hsum]
    exact hdiffsmall.trans_le htarget
  have hcap := cubicCauchyRelativeCapacity_gt hM hu husmall
  refine ⟨m, n, hm, hn, ?_⟩
  change M < 64 * x ^ 3 * y ^ 3 / ((x + y) ^ 6 - 64 * x ^ 3 * y ^ 3)
  rwa [← cubicCauchyRelativeCapacity_abs_sub_div_add_eq hx hy hxy]

/-- Fixed primes 2 and 3 retain a nonzero relative theta frame at every nonneutral grade. -/
def primeBurnolThetaTwoThreeMismatch (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) -
    _root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ *
      _root_.RHTower.primeBurnolThetaBlock (-a) ⟨2, Nat.prime_two⟩

theorem primeBurnolThetaTwoThreeMismatch_ne_zero
    {a : ℝ} (ha : a ≠ 0) : primeBurnolThetaTwoThreeMismatch a ≠ 0 := by
  intro hzero
  have hprod :
      _root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ *
          _root_.RHTower.primeBurnolThetaBlock (-a) ⟨2, Nat.prime_two⟩ = 1 := by
    rw [primeBurnolThetaTwoThreeMismatch] at hzero
    exact (sub_eq_zero.mp hzero).symm
  have hQeqP :
      _root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ =
        _root_.RHTower.primeBurnolThetaBlock a ⟨2, Nat.prime_two⟩ := by
    calc
      _root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ =
          _root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ * 1 := by simp
      _ = _root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ *
          (_root_.RHTower.primeBurnolThetaBlock (-a) ⟨2, Nat.prime_two⟩ *
            _root_.RHTower.primeBurnolThetaBlock a ⟨2, Nat.prime_two⟩) := by
          rw [_root_.RHTower.primeBurnolThetaBlock_neg_mul]
      _ = (_root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ *
          _root_.RHTower.primeBurnolThetaBlock (-a) ⟨2, Nat.prime_two⟩) *
            _root_.RHTower.primeBurnolThetaBlock a ⟨2, Nat.prime_two⟩ := by
              rw [Matrix.mul_assoc]
      _ = _root_.RHTower.primeBurnolThetaBlock a ⟨2, Nat.prime_two⟩ := by
        rw [hprod, Matrix.one_mul]
  have hentry := congrArg (fun M => M (1 : Fin 2) (0 : Fin 2)) hQeqP
  simp [_root_.RHTower.primeBurnolThetaBlock] at hentry
  have hpq : (⟨3, Nat.prime_three⟩ : Nat.Primes) ≠ ⟨2, Nat.prime_two⟩ := by
    intro h
    have hv := congrArg Subtype.val h
    norm_num at hv
  exact (_root_.RHTower.primeBurnolThetaContrast_ne_of_prime_ne ha hpq) hentry

theorem exists_primeBurnolThetaTwoThreeMismatch_entry_ne_zero
    {a : ℝ} (ha : a ≠ 0) :
    ∃ r s : Fin 2, primeBurnolThetaTwoThreeMismatch a r s ≠ 0 := by
  by_contra h
  push Not at h
  apply primeBurnolThetaTwoThreeMismatch_ne_zero ha
  ext r s
  exact h r s

/-- Exact retained-block correction predicted by the two-site modular holonomy law. -/
def twoThreePrimeDepthThetaModularCorrection (a : ℝ) (m n : ℕ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ((twoThreePrimeDepthCubicCauchyCapacity m n : ℝ) : ℂ) •
    primeBurnolThetaTwoThreeMismatch a

/-- For every nonneutral grade, some coefficient of the exact two-site modular correction
`capacity · (I-U₃(a)U₂(a)⁻¹)` exceeds every prescribed bound along literal positive depths. -/
theorem exists_two_three_thetaModularEscapeCoefficient_gt
    {a M : ℝ} (ha : a ≠ 0) (hM : 0 ≤ M) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      ∃ r s : Fin 2,
        M < ‖twoThreePrimeDepthThetaModularCorrection a m n r s‖ := by
  obtain ⟨r, s, hrs⟩ := exists_primeBurnolThetaTwoThreeMismatch_entry_ne_zero ha
  have hnorm : 0 < ‖primeBurnolThetaTwoThreeMismatch a r s‖ := norm_pos_iff.mpr hrs
  let B := M / ‖primeBurnolThetaTwoThreeMismatch a r s‖
  have hB : 0 ≤ B := div_nonneg hM hnorm.le
  obtain ⟨m, n, hm, hn, hcap⟩ :=
    exists_two_three_primeDepth_cubicCauchyCapacity_gt hB
  let cap : ℝ := twoThreePrimeDepthCubicCauchyCapacity m n
  change B < cap at hcap
  have hcap0 : 0 < cap := lt_of_le_of_lt hB hcap
  have hmul : M < cap * ‖primeBurnolThetaTwoThreeMismatch a r s‖ := by
    apply (div_lt_iff₀ hnorm).mp
    exact hcap
  refine ⟨m, n, hm, hn, r, s, ?_⟩
  change M < ‖(cap : ℂ) * primeBurnolThetaTwoThreeMismatch a r s‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcap0]
  exact hmul

/-- Uniform boundedness of the canonical two-prime modular correction, defined entirely before
any divisor is supplied. -/
def PrimeDepthThetaModularAdmissible (a : ℝ) : Prop :=
  ∃ M : ℝ, ∀ m n : ℕ, 0 < m → 0 < n → ∀ r s : Fin 2,
    ‖twoThreePrimeDepthThetaModularCorrection a m n r s‖ ≤ M

/-- **Pre-divisor selection law.** Canonical prime-depth theta modular transport is uniformly
admissible exactly at neutral grade. -/
theorem primeDepthThetaModularAdmissible_iff (a : ℝ) :
    PrimeDepthThetaModularAdmissible a ↔ a = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra ha
    let M := max C 0
    have hM : 0 ≤ M := le_max_right _ _
    obtain ⟨m, n, hm, hn, r, s, hescape⟩ :=
      exists_two_three_thetaModularEscapeCoefficient_gt ha hM
    have hbound := hC m n hm hn r s
    have hCM : C ≤ M := le_max_left _ _
    linarith
  · rintro rfl
    refine ⟨0, fun m n hm hn r s => ?_⟩
    simp [twoThreePrimeDepthThetaModularCorrection,
      primeBurnolThetaTwoThreeMismatch,
      _root_.RHTower.primeBurnolThetaBlock_zero]

end

end GaloisForLFunctions.RHTower
