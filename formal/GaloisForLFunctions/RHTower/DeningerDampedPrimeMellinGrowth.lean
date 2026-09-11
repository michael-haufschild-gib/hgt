import GaloisForLFunctions.RHTower.DeningerDampedPrimeCircleContraction

/-!
# Fixed negative Mellin growth of actual damped prime sources

For every original prime and damping in `[0,1]`, the paired source multiplier
has norm at least `217/32` at the fixed Mellin coordinate `-4`, and norm at
most `4` at every actual Xi coordinate. Xi normalization therefore amplifies
the negative reading by at least `217/128` per original prime/depth.

This estimate is proved for the entire literal finite product applied to
the original reflected Gaussian, with every repetition retained. The
normalized Xi reading is one. Its negative reading grows geometrically in
the list length, uniformly in damping, including a damping parameter that
changes at every stage. Cofinal prime lists have unbounded length, so these
sources escape every compact set and have no limit in the original Meyer
topology. An explicit instance uses all original primes up to `n` and
positive damping `1/(n+1)` tending to zero.

The positive survivor is a uniform growth law for a fixed original-source
continuous functional. This does not preclude weaker distributional source
topologies where that functional is discontinuous. It does not identify
the original complete Green/BV boundary with the fixed physical reader,
assert a vanishing physical image, or prove RH.
-/

open Complex Filter Topology SchwartzMap
namespace RHTower
noncomputable section

/-- The literal multiplier at a real Mellin coordinate is real. -/
theorem deningerDampedPairedMultiplier_ofReal (L a s : ℝ) :
    deningerDampedPairedMultiplier L a (s : ℂ) =
      (((1 - deningerDampedPrimeWeight L a * Real.exp (-L*s)) *
        (1 - deningerDampedPrimeWeight L a * Real.exp (-L*(1-s))) : ℝ) : ℂ) := by
  simp only [deningerDampedPairedMultiplier, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_exp, Complex.ofReal_neg]

/-- The original open strip gives a uniform bound without critical-line placement. -/
theorem deningerDampedPairedMultiplier_norm_le_four (L a : ℝ) (hL : 0 ≤ L)
    (ha : 0 ≤ a) (s : ℂ) (hs : 0 ≤ s.re ∧ s.re ≤ 1) :
    ‖deningerDampedPairedMultiplier L a s‖ ≤ 4 := by
  have hc (v : ℂ) (hv : 0 ≤ v.re) :
      ‖(deningerDampedPrimeWeight L a : ℂ) * Complex.exp ((-L : ℂ)*v)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, deningerDampedPrimeWeight,
      abs_of_pos (Real.exp_pos _), Complex.norm_exp]
    rw [← Real.exp_add, Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    exact add_nonpos (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hL)
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) hv)
  have hf (v : ℂ) (hv : 0 ≤ v.re) :
      ‖1 - (deningerDampedPrimeWeight L a : ℂ)*Complex.exp ((-L : ℂ)*v)‖ ≤ 2 := by
    calc _ ≤ ‖(1 : ℂ)‖ + ‖(deningerDampedPrimeWeight L a : ℂ)*Complex.exp ((-L : ℂ)*v)‖ := norm_sub_le _ _
         _ ≤ 2 := by rw [norm_one]; linarith [hc v hv]
  rw [deningerDampedPairedMultiplier, norm_mul]
  have h1 := hf s hs.1
  have h2 := hf (1-s) (by simp only [Complex.sub_re, Complex.one_re]; linarith [hs.2])
  nlinarith [norm_nonneg (1 - (deningerDampedPrimeWeight L a : ℂ)*Complex.exp ((-L : ℂ)*s)),
    norm_nonneg (1 - (deningerDampedPrimeWeight L a : ℂ)*Complex.exp ((-L : ℂ)*(1-s)))]

/-- Every original prime amplifies the fixed negative coordinate uniformly for bounded damping. -/
theorem deningerDampedPairedMultiplier_negative_four_lower (p : Nat.Primes)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (217/32 : ℝ) ≤ ‖deningerDampedPairedMultiplier (Real.log (p : ℕ)) a (-4)‖ := by
  let L := Real.log (p : ℕ)
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.two_le
  have hL : 0 < L := Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hp2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hU : 8 ≤ deningerDampedPrimeWeight L a * Real.exp (-L*(-4)) := by
    rw [deningerDampedPrimeWeight, ← Real.exp_add]
    have he : Real.exp ((3 : ℝ)*Real.log 2) = 8 := by
      rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log (by norm_num)]
      norm_num
    rw [← he]
    apply Real.exp_le_exp.mpr
    have := mul_nonneg (sub_nonneg.mpr ha1) hL.le
    nlinarith
  have hV : deningerDampedPrimeWeight L a * Real.exp (-L*(1-(-4))) ≤ (1/32 : ℝ) := by
    rw [deningerDampedPrimeWeight, ← Real.exp_add]
    have he : Real.exp (-(5 : ℝ)*Real.log 2) = 1/32 := by
      rw [neg_mul, Real.exp_neg]
      have he5 : Real.exp ((5 : ℝ)*Real.log 2) = 32 := by
        rw [show (5 : ℝ) = (5 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log (by norm_num)]
        norm_num
      rw [he5]
      norm_num
    rw [← he]
    apply Real.exp_le_exp.mpr
    have := mul_nonneg ha hL.le
    nlinarith
  rw [show (-4 : ℂ) = ((-4 : ℝ) : ℂ) by norm_num]
  change (217/32 : ℝ) ≤ ‖deningerDampedPairedMultiplier L a ((-4 : ℝ) : ℂ)‖
  rw [deningerDampedPairedMultiplier_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hprod : (1 - deningerDampedPrimeWeight L a * Real.exp (-L*(-4))) *
      (1 - deningerDampedPrimeWeight L a * Real.exp (-L*(1-(-4)))) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr ((by norm_num : (1 : ℝ) ≤ 8).trans hU))
      (sub_nonneg.mpr (hV.trans (by norm_num)))
  rw [abs_of_nonpos hprod]
  have hb : (217/32 : ℝ) ≤
      (deningerDampedPrimeWeight L a * Real.exp (-L*(-4)) - 1) *
        (1 - deningerDampedPrimeWeight L a * Real.exp (-L*(1-(-4)))) := by
    calc (217/32 : ℝ) = 7*(31/32) := by ring
         _ ≤ _ := mul_le_mul (by linarith only [hU]) (by linarith only [hV])
           (by norm_num) (by linarith only [hU])
  nlinarith only [hb]

/-- Uniform growth per original prime/depth after retaining the actual Xi coefficient. -/
theorem deningerDampedPairedMultiplier_normalized_negative_lower (p : Nat.Primes)
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (rho : XiDivisorSupport) :
    (217/128 : ℝ) ≤ ‖deningerDampedPairedMultiplier (Real.log (p : ℕ)) a (-4) /
      deningerDampedPairedMultiplier (Real.log (p : ℕ)) a rho‖ := by
  have hL : 0 < Real.log (p : ℕ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hs := xi_divisor_support_re_mem_open_unit rho
  have hpos := norm_pos_iff.mpr (deningerDampedPairedMultiplier_ne_zero _ a hL ha rho hs)
  rw [norm_div, le_div_iff₀ hpos]
  have hupper := deningerDampedPairedMultiplier_norm_le_four _ a hL.le ha rho ⟨hs.1.le, hs.2.le⟩
  have hlower := deningerDampedPairedMultiplier_negative_four_lower p a ha ha1
  nlinarith

/-- Ordered actual finite prime product, retaining repetitions. -/
def deningerDampedPrimeListSource (a : ℝ) : List Nat.Primes → DeningerMeyerStrongLogTarget
  | [] => deningerMeyerReflectedLogGaussianSource
  | p :: P => deningerDampedPairedStrongLogDefect (Real.log (p : ℕ)) a
      (deningerDampedPrimeListSource a P)

def deningerDampedPrimeListMultiplier (a : ℝ) (P : List Nat.Primes) (s : ℂ) : ℂ :=
  (P.map fun (p : Nat.Primes) => deningerDampedPairedMultiplier (Real.log (p : ℕ)) a s).prod

theorem deningerDampedPrimeListSource_mellin (a : ℝ) (P : List Nat.Primes) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerDampedPrimeListSource a P) s =
      deningerDampedPrimeListMultiplier a P s *
        deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource s := by
  induction P with
  | nil => simp [deningerDampedPrimeListSource, deningerDampedPrimeListMultiplier]
  | cons p P ih =>
    rw [deningerDampedPrimeListSource, deningerDampedPairedStrongLogDefect_mellin, ih]
    simp only [deningerDampedPrimeListMultiplier, List.map_cons, List.prod_cons]
    ring

theorem deningerDampedPrimeListSource_J_fixed (a : ℝ) (P : List Nat.Primes) :
    deningerMeyerStrongLogJ (deningerDampedPrimeListSource a P) =
      deningerDampedPrimeListSource a P := by
  induction P with
  | nil => exact deningerMeyerReflectedLogGaussianSource_J_fixed
  | cons p P ih =>
    rw [deningerDampedPrimeListSource, deningerDampedPairedStrongLogDefect_J, ih]

theorem deningerDampedPrimeListSource_xi_ne_zero (a : ℝ) (ha : 0 ≤ a)
    (P : List Nat.Primes) (rho : XiDivisorSupport) :
    deningerMeyerStrongLogMellin (deningerDampedPrimeListSource a P) rho ≠ 0 := by
  induction P with
  | nil => exact deningerMeyerReflectedLogGaussianSource_mellin_ne_zero rho
  | cons p P ih =>
    rw [deningerDampedPrimeListSource, deningerDampedPairedStrongLogDefect_mellin]
    exact mul_ne_zero (deningerDampedPairedMultiplier_ne_zero _ a
      (Real.log_pos (by exact_mod_cast p.property.one_lt)) ha rho
      (xi_divisor_support_re_mem_open_unit rho)) ih

def deningerDampedPrimeListNormalized (a : ℝ) (P : List Nat.Primes)
    (rho : XiDivisorSupport) : DeningerMeyerSource :=
  (deningerMeyerStrongLogMellin (deningerDampedPrimeListSource a P) rho)⁻¹ •
    deningerDampedStrongLogOriginalSourceLM (deningerDampedPrimeListSource a P)

theorem deningerDampedPrimeListNormalized_reading (a : ℝ) (ha : 0 ≤ a)
    (P : List Nat.Primes) (rho : XiDivisorSupport) :
    deningerOriginalMeyerMellinCLM rho (deningerDampedPrimeListNormalized a P rho) = 1 := by
  rw [deningerDampedPrimeListNormalized, map_smul, deningerDampedStrongLogOriginalSourceLM_mellin,
    smul_eq_mul, inv_mul_cancel₀ (deningerDampedPrimeListSource_xi_ne_zero a ha P rho)]

/-- Exact two-point reading ratio of the full original source. -/
theorem deningerDampedPrimeListNormalized_mellin (a : ℝ) (P : List Nat.Primes)
    (rho : XiDivisorSupport) (s : ℂ) :
    deningerOriginalMeyerMellinCLM s (deningerDampedPrimeListNormalized a P rho) =
      (deningerDampedPrimeListMultiplier a P s / deningerDampedPrimeListMultiplier a P rho) *
        (deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource s /
          deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource rho) := by
  rw [deningerDampedPrimeListNormalized, map_smul, deningerDampedStrongLogOriginalSourceLM_mellin,
    smul_eq_mul, deningerDampedPrimeListSource_mellin, deningerDampedPrimeListSource_mellin]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem deningerDampedPrimeListMultiplier_negative_ratio_lower (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (P : List Nat.Primes) (rho : XiDivisorSupport) :
    (217/128 : ℝ)^P.length ≤
      ‖deningerDampedPrimeListMultiplier a P (-4) / deningerDampedPrimeListMultiplier a P rho‖ := by
  induction P with
  | nil => simp [deningerDampedPrimeListMultiplier]
  | cons p P ih =>
    change (217/128 : ℝ)^(P.length+1) ≤
      ‖(deningerDampedPairedMultiplier (Real.log (p : ℕ)) a (-4) *
        deningerDampedPrimeListMultiplier a P (-4)) /
        (deningerDampedPairedMultiplier (Real.log (p : ℕ)) a rho *
          deningerDampedPrimeListMultiplier a P rho)‖
    rw [mul_div_mul_comm, norm_mul, pow_succ, mul_comm ((217/128 : ℝ)^P.length)]
    exact mul_le_mul (deningerDampedPairedMultiplier_normalized_negative_lower p a ha ha1 rho)
      ih (pow_nonneg (by norm_num) _) (norm_nonneg _)

/-- The entire remaining source grows at a fixed continuous Mellin reading. -/
theorem deningerDampedPrimeListNormalized_negative_lower (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (P : List Nat.Primes) (rho : XiDivisorSupport) :
    (217/128 : ℝ)^P.length *
      ‖deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource (-4) /
        deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource rho‖ ≤
    ‖deningerOriginalMeyerMellinCLM (-4) (deningerDampedPrimeListNormalized a P rho)‖ := by
  rw [deningerDampedPrimeListNormalized_mellin, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (deningerDampedPrimeListMultiplier_negative_ratio_lower a ha ha1 P rho) (norm_nonneg _)

/-- Uniformity in damping allows it to vary at every finite stage. -/
theorem deningerDampedPrimeListNormalized_negative_tendsto
    (P : ℕ → List Nat.Primes) (hP : Tendsto (fun n => (P n).length) atTop atTop)
    (a : ℕ → {x : ℝ // 0 ≤ x ∧ x ≤ 1}) (rho : XiDivisorSupport) :
    Tendsto (fun n => ‖deningerOriginalMeyerMellinCLM (-4)
      (deningerDampedPrimeListNormalized (a n) (P n) rho)‖) atTop atTop := by
  have hg : 0 < ‖deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource (-4) /
      deningerMeyerStrongLogMellin deningerMeyerReflectedLogGaussianSource rho‖ :=
    norm_pos_iff.mpr (div_ne_zero (deningerMeyerReflectedLogGaussianSource_mellin_ne_zero _)
      (deningerMeyerReflectedLogGaussianSource_mellin_ne_zero _))
  have hexp := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 217/128)).comp hP
  exact Filter.tendsto_atTop_mono (fun n =>
    deningerDampedPrimeListNormalized_negative_lower (a n) (a n).property.1
      (a n).property.2 (P n) rho) (hexp.atTop_mul_const hg)

/-- A fixed original-source functional forces compact escape for the whole damped product. -/
theorem deningerDampedPrimeListNormalized_compact_escape
    (P : ℕ → List Nat.Primes) (hP : Tendsto (fun n => (P n).length) atTop atTop)
    (a : ℕ → {x : ℝ // 0 ≤ x ∧ x ≤ 1}) (rho : XiDivisorSupport)
    (K : Set DeningerMeyerSource) (hK : IsCompact K) :
    ∀ᶠ n in atTop, deningerDampedPrimeListNormalized (a n) (P n) rho ∉ K := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image (deningerOriginalMeyerMellinCLM (-4)).continuous.norm.continuousOn
  have ht := deningerDampedPrimeListNormalized_negative_tendsto P hP a rho
  filter_upwards [ht.eventually (eventually_gt_atTop C)] with n hn hmem
  exact (not_le_of_gt hn) (hC (Set.mem_image_of_mem _ hmem))

/-- Cofinality of original primes forces unbounded length, with repetitions allowed. -/
theorem deningerCofinalPrimeList_length_tendsto (P : ℕ → List Nat.Primes)
    (hP : ∀ p : Nat.Primes, ∀ᶠ n in atTop, p ∈ P n) :
    Tendsto (fun n => (P n).length) atTop atTop := by
  have hF : Tendsto (fun n => (P n).toFinset) atTop atTop := by
    simp only [Filter.atTop_finset_eq_iInf, tendsto_iInf, tendsto_principal]
    intro p
    filter_upwards [hP p] with n hn
    exact Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr hn)
  exact Filter.tendsto_atTop_mono (fun n => (P n).toFinset_card_le)
    (Filter.tendsto_card_atTop_atTop.comp hF)

/-- Explicit original prime prefixes: every bounded-damping normalized family escapes. -/
theorem deningerDampedPrimePrefix_compact_escape
    (a : ℕ → {x : ℝ // 0 ≤ x ∧ x ≤ 1}) (rho : XiDivisorSupport) :
    ∀ K : Set DeningerMeyerSource, IsCompact K → ∀ᶠ n in atTop,
      deningerDampedPrimeListNormalized (a n) (GaloisForLFunctions.primesLE n).toList rho ∉ K := by
  intro K hK
  exact deningerDampedPrimeListNormalized_compact_escape _
    (deningerCofinalPrimeList_length_tendsto _ deningerOriginalPrimePrefix_cofinal) a rho K hK

/-- The same growth holds for every repeated depth of one fixed original prime. -/
theorem deningerDampedRepeatedPrime_compact_escape (p : Nat.Primes)
    (a : ℕ → {x : ℝ // 0 ≤ x ∧ x ≤ 1}) (rho : XiDivisorSupport) :
    ∀ K : Set DeningerMeyerSource, IsCompact K → ∀ᶠ n in atTop,
      deningerDampedPrimeListNormalized (a n) (List.replicate n p) rho ∉ K := by
  intro K hK
  exact deningerDampedPrimeListNormalized_compact_escape (fun n => List.replicate n p)
    (by simp only [List.length_replicate]; exact tendsto_id) a rho K hK


/-- The divergent fixed reading excludes any original-Meyer source limit. -/
theorem deningerDampedPrimeListNormalized_not_tendsto
    (P : ℕ → List Nat.Primes) (hP : Tendsto (fun n => (P n).length) atTop atTop)
    (a : ℕ → {x : ℝ // 0 ≤ x ∧ x ≤ 1}) (rho : XiDivisorSupport) (h : DeningerMeyerSource) :
    ¬ Tendsto (fun n => deningerDampedPrimeListNormalized (a n) (P n) rho) atTop (nhds h) := by
  intro hh
  exact not_tendsto_atTop_of_tendsto_nhds
    (((deningerOriginalMeyerMellinCLM (-4)).continuous.norm.tendsto h).comp hh)
    (deningerDampedPrimeListNormalized_negative_tendsto P hP a rho)

/-- Unconditional no-limit theorem for the explicit damped original-prime prefixes. -/
theorem deningerDampedPrimePrefix_no_limit
    (a : ℕ → {x : ℝ // 0 ≤ x ∧ x ≤ 1}) (rho : XiDivisorSupport) :
    ¬ ∃ h : DeningerMeyerSource, Tendsto (fun n =>
      deningerDampedPrimeListNormalized (a n) (GaloisForLFunctions.primesLE n).toList rho)
      atTop (nhds h) := by
  rintro ⟨h, hh⟩
  exact deningerDampedPrimeListNormalized_not_tendsto _
    (deningerCofinalPrimeList_length_tendsto _ deningerOriginalPrimePrefix_cofinal) a rho h hh

/-- An explicit positive damping tending to zero, with no sequence hypothesis. -/
def deningerVanishingPrimeDamping (n : ℕ) : {x : ℝ // 0 ≤ x ∧ x ≤ 1} :=
  ⟨1 / ((n : ℝ)+1), by
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ)+1)).mpr
      exact le_add_of_nonneg_left (Nat.cast_nonneg n)⟩

theorem deningerVanishingPrimeDamping_tendsto :
    Tendsto (fun n => (deningerVanishingPrimeDamping n : ℝ)) atTop (nhds 0) := by
  simpa only [deningerVanishingPrimeDamping] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) atTop (nhds 0))

/-- The explicit vanishing-damping original-prime prefix has no original source limit. -/
theorem deningerVanishingDampedPrimePrefix_no_limit (rho : XiDivisorSupport) :
    ¬ ∃ h : DeningerMeyerSource, Tendsto (fun n =>
      deningerDampedPrimeListNormalized (deningerVanishingPrimeDamping n)
        (GaloisForLFunctions.primesLE n).toList rho) atTop (nhds h) :=
  deningerDampedPrimePrefix_no_limit deningerVanishingPrimeDamping rho

theorem deningerVanishingDampedPrimePrefix_compact_escape (rho : XiDivisorSupport) :
    ∀ K : Set DeningerMeyerSource, IsCompact K → ∀ᶠ n in atTop,
      deningerDampedPrimeListNormalized (deningerVanishingPrimeDamping n)
        (GaloisForLFunctions.primesLE n).toList rho ∉ K :=
  deningerDampedPrimePrefix_compact_escape deningerVanishingPrimeDamping rho

end
end RHTower
