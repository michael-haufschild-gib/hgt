import GaloisForLFunctions.RHTower.WeilWorkPBAPPacketFourier
import GaloisForLFunctions.RHTower.LebesgueAtomWeilPositivity
/-!
# Full energy growth of narrow integer packets

The actual smooth packets obey a uniform logarithmic lower bound for the full
pole-plus-gamma functional. Both signed pole terms are controlled together.
Arbitrary complex coefficients are allowed; no integer-null or positivity
premise is imposed. This restricted-family diagnostic does not prove PBAP.
-/
open Complex MeasureTheory Zeta23
open scoped BigOperators ComplexConjugate
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

theorem gammaBracket_lower (t : ℝ) :
    Real.log (1+|t|/4)-10 ≤ EF.gammaBracket t := by
  have h := log_sub_seven_le_re_digamma_quarter t
  have hpi : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_d2]
  unfold EF.gammaBracket
  linarith

theorem gramPacket_gamma_lower (N L : ℕ) (hL : 104 ≤ L) (c : ℕ → ℂ) :
    packetMass N L * (∑ n ∈ Finset.Icc 1 N, ‖c n‖^2) *
        ((1/2)*Real.log (1+((N*L:ℕ):ℝ)/4)-10) ≤
      (1/(2*Real.pi)) * ∫ t : ℝ,
        ‖paperFT (gramPacket N L c) (t:ℂ)‖^2 * EF.gammaBracket t := by
  let f := gramPacket N L c
  let D : ℝ → ℝ := fun t => ‖paperFT f (t:ℂ)‖^2
  let T : ℝ := ((N*L:ℕ):ℝ)
  let M := packetMass N L * ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2
  let q := Real.log (1+T/4)
  let s := Set.Ioc (-T) T
  have hf : ContDiff ℝ 2 f := (contDiff_gramPacket N L c).of_le (by norm_cast)
  have hfc : HasCompactSupport f := hasCompactSupport_gramPacket N L c
  obtain ⟨a, ha⟩ := WeilSpectral.exists_abs_bound_of_hasCompactSupport hfc
  have hfs : tsupport f ⊆ Set.Icc (-a) a := tsupport_subset_of_vanish
    (fun u hu => by by_contra h; exact (not_le_of_gt hu) (ha u h))
  have hD : Integrable D := integrable_normSq_paperFT hf hfs
  have hGc := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hf hfc hf hfc
  have hG : Integrable (fun t => D t * EF.gammaBracket t) := by
    refine hGc.re.congr (Filter.Eventually.of_forall fun t => ?_)
    change (paperFT (EF.weilTest f f) (t:ℂ) * (EF.gammaBracket t:ℂ)).re = D t*EF.gammaBracket t
    rw [paperFT_weilTest_self_ofReal hf.continuous hfc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rfl
  have hplus_eq : (fun t => D t*(EF.gammaBracket t+10)) =
      (fun t => D t*EF.gammaBracket t+10*D t) := by funext t; ring
  have hplus : Integrable (fun t => D t*(EF.gammaBracket t+10)) := by
    rw [hplus_eq]
    exact hG.add (hD.const_mul 10)
  have hnn : ∀ t, 0 ≤ D t*(EF.gammaBracket t+10) := by
    intro t
    apply mul_nonneg (sq_nonneg _)
    have hlog := Real.log_nonneg (show 1 ≤ 1+|t|/4 by linarith [abs_nonneg t])
    have hg := gammaBracket_lower t
    linarith
  have hq : 0 ≤ q := Real.log_nonneg (by
    have hT : 0 ≤ T := Nat.cast_nonneg _
    linarith)
  have hM : 0 ≤ M := mul_nonneg (packetMass_pos N L).le
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hstep : q * (∫ t in sᶜ, D t) ≤ ∫ t in sᶜ, D t*(EF.gammaBracket t+10) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hD.const_mul q).integrableOn hplus.integrableOn
      measurableSet_Ioc.compl
    intro t ht
    have habs : T ≤ |t| := by
      by_contra h
      have ht' := abs_lt.mp (lt_of_not_ge h)
      exact ht ⟨ht'.1, ht'.2.le⟩
    have hlog : q ≤ Real.log (1+|t|/4) :=
      Real.log_le_log (by dsimp [T]; positivity) (by linarith)
    have hg := gammaBracket_lower t
    have hh : q ≤ EF.gammaBracket t+10 := by linarith
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (sq_nonneg (‖paperFT f (t:ℂ)‖))
  have htot := LebesgueAtomWeil.integral_norm_sq_paperFT_eq hf hfc
  change (1/(2*Real.pi)) * (∫ t, D t) = ∫ u, ‖gramPacket N L c u‖^2 at htot
  rw [gramPacket_mass N L (by omega) c] at htot
  change (1/(2*Real.pi)) * (∫ t, D t) = M at htot
  have htotal : (∫ t, D t) = M*(2*Real.pi) := by
    rw [one_div_mul_eq_div] at htot
    have hden : (2*Real.pi:ℝ) ≠ 0 := by positivity
    field_simp [hden] at htot
    nlinarith
  have hlow : (∫ t in s, D t) ≤ 2*M := by
    have hl := gramPacket_low_mass_le N L hL c
    rw [intervalIntegral.integral_of_le (by
      have hh := (Nat.cast_nonneg (N*L) : (0:ℝ) ≤ (N*L:ℕ))
      linarith)] at hl
    simpa only [M, mul_assoc] using hl
  have hall := setIntegral_le_integral (s := sᶜ) hplus (Filter.Eventually.of_forall hnn)
  have hs := hstep.trans hall
  rw [hplus_eq, integral_add hG (hD.const_mul 10), integral_const_mul,
    setIntegral_compl measurableSet_Ioc hD, htotal] at hs
  change M*((1/2)*q-10) ≤ (1/(2*Real.pi)) * ∫ t, D t*EF.gammaBracket t
  simp only [one_div_mul_eq_div]
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).2
  have hh := mul_le_mul_of_nonneg_left hlow hq
  have hp : 0 ≤ q*M*(Real.pi-2) :=
    mul_nonneg (mul_nonneg hq hM) (by linarith [Real.pi_gt_three])
  nlinarith
/-- Finite Cauchy–Schwarz at a complex Fourier argument. -/
theorem norm_paperFT_gramPacket_sq_le (N L : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    ‖paperFT (gramPacket N L c) z‖^2 ≤
      ‖paperFT (narrowBumpC (N*L)) z‖^2 *
        (∑ n ∈ Finset.Icc 1 N, ‖c n‖^2) *
        ∑ n ∈ Finset.Icc 1 N, Real.exp (-2*z.im*resPt N n) := by
  classical
  let w := fun n => Real.exp (-z.im*resPt N n)
  have he (n : ℕ) : ‖Complex.exp (I*z*(resPt N n:ℂ))‖ = w n := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  have hn : ‖∑ n ∈ Finset.Icc 1 N, c n*Complex.exp (I*z*(resPt N n:ℂ))‖ ≤
      ∑ n ∈ Finset.Icc 1 N, ‖c n‖*w n := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖c n*Complex.exp (I*z*(resPt N n:ℂ))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, he]
  have hw : ∀ n, 0 ≤ w n := fun n => (Real.exp_pos _).le
  have hs : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖c n‖*w n :=
    Finset.sum_nonneg fun n _ => mul_nonneg (norm_nonneg _) (hw n)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N) (fun n => ‖c n‖) w
  have hw2 : ∑ n ∈ Finset.Icc 1 N, (w n)^2 =
      ∑ n ∈ Finset.Icc 1 N, Real.exp (-2*z.im*resPt N n) := by
    apply Finset.sum_congr rfl
    intro n _
    dsimp [w]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hw2] at hcs
  have hn2 : ‖∑ n ∈ Finset.Icc 1 N, c n*Complex.exp (I*z*(resPt N n:ℂ))‖^2 ≤
      (∑ n ∈ Finset.Icc 1 N, ‖c n‖^2) *
        ∑ n ∈ Finset.Icc 1 N, Real.exp (-2*z.im*resPt N n) := by
    have hnn := norm_nonneg (∑ n ∈ Finset.Icc 1 N, c n*Complex.exp (I*z*(resPt N n:ℂ)))
    nlinarith
  rw [paperFT_gramPacket, norm_mul, mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left hn2 (sq_nonneg _)

/-- Centering cancels exactly between the two exponential pole weights. -/
theorem packet_pole_weight_product (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, Real.exp (-resPt N n)) *
      (∑ n ∈ Finset.Icc 1 N, Real.exp (resPt N n)) =
      (∑ n ∈ Finset.Icc 1 N, 1/(n:ℝ)) * ∑ n ∈ Finset.Icc 1 N, (n:ℝ) := by
  have hp : ∑ n ∈ Finset.Icc 1 N, Real.exp (resPt N n) =
      (∑ n ∈ Finset.Icc 1 N, (n:ℝ)) * (Real.exp (Real.log N/2))⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0 < (n:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [resPt, Real.exp_sub, Real.exp_log hn0, div_eq_mul_inv]
  have hm : ∑ n ∈ Finset.Icc 1 N, Real.exp (-resPt N n) =
      Real.exp (Real.log N/2) * (∑ n ∈ Finset.Icc 1 N, 1/(n:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0 < (n:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [resPt, neg_sub, Real.exp_sub, Real.exp_log hn0]
    ring
  rw [hp, hm]
  calc
    _ = (∑ n ∈ Finset.Icc 1 N, 1/(n:ℝ)) * (∑ n ∈ Finset.Icc 1 N, (n:ℝ)) *
        (Real.exp (Real.log N/2) * (Real.exp (Real.log N/2))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ (Real.exp_ne_zero _), mul_one]

/-- Harmonic growth, rather than a square-root loss in the packet count. -/
theorem packet_pole_weight_product_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, Real.exp (-resPt N n)) *
      (∑ n ∈ Finset.Icc 1 N, Real.exp (resPt N n)) ≤
      (N:ℝ)^2 * (1+Real.log N) := by
  rw [packet_pole_weight_product]
  have hh := Sieve.sum_Icc_one_div_le_one_add_log N
  have hh0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, 1/(n:ℝ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hn0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, (n:ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hn : ∑ n ∈ Finset.Icc 1 N, (n:ℝ) ≤ (N:ℝ)^2 := by
    calc
      _ ≤ ∑ _n ∈ Finset.Icc 1 N, (N:ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        exact_mod_cast (Finset.mem_Icc.mp hn).2
      _ = _ := by simp [Nat.card_Icc, pow_two]
  calc
    _ ≤ (1+Real.log N) * (N:ℝ)^2 := mul_le_mul hh hn hn0 (hh0.trans hh)
    _ = _ := by ring

/-- Both complex pole evaluations are controlled together; centering cancels. -/
theorem gramPacket_pole_norm_product_le (N L : ℕ) (c : ℕ → ℂ) :
    ‖paperFT (gramPacket N L c) (I/2)‖ *
      ‖paperFT (gramPacket N L c) (-I/2)‖ ≤
      Real.exp (1/(4*((N*L:ℕ)+1:ℝ))) * (packetL1 N L)^2 *
        (∑ n ∈ Finset.Icc 1 N, ‖c n‖^2) * N * Real.sqrt (1+Real.log N) := by
  let r : ℝ := 1/(4*((N*L:ℕ)+1:ℝ))
  let S := ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2
  let X := ∑ n ∈ Finset.Icc 1 N, Real.exp (resPt N n)
  let Y := ∑ n ∈ Finset.Icc 1 N, Real.exp (-resPt N n)
  let B := Real.exp r * (packetL1 N L)^2 * S
  let ap := ‖paperFT (gramPacket N L c) (I/2)‖
  let am := ‖paperFT (gramPacket N L c) (-I/2)‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hX : 0 ≤ X := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hY : 0 ≤ Y := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) hS
  have hH : 0 ≤ 1+Real.log N :=
    (Finset.sum_nonneg fun n (_ : n ∈ Finset.Icc 1 N) =>
      (by positivity : (0:ℝ) ≤ 1/(n:ℝ))).trans (Sieve.sum_Icc_one_div_le_one_add_log N)
  have hb : ∀ z : ℂ, |z.im| = 1/2 →
      ‖paperFT (narrowBumpC (N*L)) z‖^2 ≤ Real.exp r*(packetL1 N L)^2 := by
    intro z hz
    have h := norm_paperFT_narrowBumpC_le N L z
    rw [hz] at h
    change ‖paperFT (narrowBumpC (N*L)) z‖ ≤ Real.exp (r*(1/2))*packetL1 N L at h
    have he : (Real.exp (r*(1/2))*packetL1 N L)^2 = Real.exp r*(packetL1 N L)^2 := by
      rw [mul_pow, pow_two, ← Real.exp_add]
      congr 2
      ring
    have hn := norm_nonneg (paperFT (narrowBumpC (N*L)) z)
    have he0 : 0 ≤ Real.exp (r*(1/2))*packetL1 N L :=
      mul_nonneg (Real.exp_pos _).le (packetL1_nonneg N L)
    nlinarith
  have hpi : ((I/2:ℂ).im) = 1/2 := by norm_num
  have hmi : ((-I/2:ℂ).im) = -(1/2) := by norm_num
  have hp : ap^2 ≤ B*Y := by
    have h := norm_paperFT_gramPacket_sq_le N L c (I/2)
    rw [hpi] at h
    norm_num only [show -(2:ℝ)*(1/2) = -1 by norm_num, neg_one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hb _ (by rw [hpi]; norm_num)) hS) hY)
  have hm : am^2 ≤ B*X := by
    have h := norm_paperFT_gramPacket_sq_le N L c (-I/2)
    rw [hmi] at h
    norm_num only [show -(2:ℝ)*(-(1/2)) = 1 by norm_num, one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hb _ (by rw [hmi]; norm_num)) hS) hX)
  have hab := mul_le_mul hp hm (sq_nonneg am) (mul_nonneg hB hY)
  have hxy : Y*X ≤ (N:ℝ)^2*(1+Real.log N) := packet_pole_weight_product_le N
  have hab2 : (ap*am)^2 ≤ (B*N*Real.sqrt (1+Real.log N))^2 := by
    calc
      _ = ap^2*am^2 := by ring
      _ ≤ (B*Y)*(B*X) := hab
      _ = B^2*(Y*X) := by ring
      _ ≤ B^2*((N:ℝ)^2*(1+Real.log N)) := mul_le_mul_of_nonneg_left hxy (sq_nonneg B)
      _ = _ := by simp only [mul_pow, Real.sq_sqrt hH]; ring
  have hn : 0 ≤ ap*am := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hr : 0 ≤ B*N*Real.sqrt (1+Real.log N) := by positivity
  change ap*am ≤ B*N*Real.sqrt (1+Real.log N)
  nlinarith

/-- The signed sum of both pole terms is explicitly retained. -/
theorem gramPacket_poles_lower (N L : ℕ) (hL : 104 ≤ L) (c : ℕ → ℂ) :
    -(2/(L:ℝ))*packetMass N L*(∑ n ∈ Finset.Icc 1 N, ‖c n‖^2)*
        Real.sqrt (1+Real.log N) ≤
      (paperFT (EF.weilTest (gramPacket N L c) (gramPacket N L c)) (I/2) +
        paperFT (EF.weilTest (gramPacket N L c) (gramPacket N L c)) (-I/2)).re := by
  let f := gramPacket N L c
  let r : ℝ := 1/(4*((N*L:ℕ)+1:ℝ))
  have hL0 : 0 < (L:ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hM := (packetMass_pos N L).le
  have hS : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr : r ≤ 1/4 := by
    dsimp [r]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith [(Nat.cast_nonneg (N*L) : (0:ℝ) ≤ (N*L:ℕ))]
  have he : Real.exp r ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval hr0 (by linarith)
    have hh : 1/(1-r) ≤ 2 := (div_le_iff₀ (by linarith)).2 (by linarith)
    exact h.trans hh
  have ha : (N:ℝ)/(((N*L:ℕ):ℝ)+1) ≤ 1/(L:ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hL0).2
    push_cast
    nlinarith
  have hp : ‖paperFT f (I/2)‖*‖paperFT f (-I/2)‖ ≤
      (1/(L:ℝ))*packetMass N L*(∑ n ∈ Finset.Icc 1 N, ‖c n‖^2)*
        Real.sqrt (1+Real.log N) := by
    calc
      _ ≤ Real.exp r*(packetL1 N L)^2*(∑ n ∈ Finset.Icc 1 N, ‖c n‖^2)*
          N*Real.sqrt (1+Real.log N) := gramPacket_pole_norm_product_le N L c
      _ ≤ 2*((2/(4*(((N*L:ℕ):ℝ)+1)))*packetMass N L)*
          (∑ n ∈ Finset.Icc 1 N, ‖c n‖^2)*N*Real.sqrt (1+Real.log N) := by
        gcongr
        exact packetL1_sq_le N L
      _ = ((N:ℝ)/(((N*L:ℕ):ℝ)+1))*packetMass N L*
          (∑ n ∈ Finset.Icc 1 N, ‖c n‖^2)*Real.sqrt (1+Real.log N) := by
        field_simp
        ring
      _ ≤ _ := by gcongr
  have hfc : HasCompactSupport f := hasCompactSupport_gramPacket N L c
  have hcont : Continuous f := (contDiff_gramPacket N L c).continuous
  have hconjp : conj (I/2:ℂ) = -I/2 := by
    simp only [map_div₀, map_ofNat, Complex.conj_I]
  have hconjm : conj (-I/2:ℂ) = I/2 := by
    simp only [map_div₀, map_ofNat, map_neg, Complex.conj_I, neg_neg]
  have hpp := EF.paperFT_weilTest hcont hcont hfc hfc (I/2)
  have hpm := EF.paperFT_weilTest hcont hcont hfc hfc (-I/2)
  rw [hconjp] at hpp
  rw [hconjm] at hpm
  have hpRe := (abs_le.mp (Complex.abs_re_le_norm
    (paperFT f (I/2) * conj (paperFT f (-I/2))))).1
  have hmRe := (abs_le.mp (Complex.abs_re_le_norm
    (paperFT f (-I/2) * conj (paperFT f (I/2))))).1
  simp only [norm_mul, Complex.norm_conj] at hpRe hmRe
  change _ ≤ (paperFT (EF.weilTest f f) (I/2)+paperFT (EF.weilTest f f) (-I/2)).re
  rw [hpp, hpm, Complex.add_re]
  simp only [div_eq_mul_inv, one_mul] at hp hpRe hmRe ⊢
  nlinarith only [hp, hpRe, hmRe]

/-- Full pole-plus-gamma lower bound for arbitrary coefficients in the actual narrow packet family. -/
theorem gramPacket_full_energy_lower (N L : ℕ) (hL : 104 ≤ L) (c : ℕ → ℂ) :
    packetMass N L * (∑ n ∈ Finset.Icc 1 N, ‖c n‖^2) *
        ((1/2)*Real.log (1+((N*L:ℕ):ℝ)/4)-10-
          (2/(L:ℝ))*Real.sqrt (1+Real.log N)) ≤
      weilArchRe (EF.weilTest (gramPacket N L c) (gramPacket N L c)) := by
  let f := gramPacket N L c
  have hcont : Continuous f := (contDiff_gramPacket N L c).continuous
  have hfc : HasCompactSupport f := hasCompactSupport_gramPacket N L c
  have hG : (∫ t : ℝ, paperFT (EF.weilTest f f) t * (EF.gammaBracket t:ℂ)) =
      ((∫ t : ℝ, ‖paperFT f (t:ℂ)‖^2*EF.gammaBracket t : ℝ):ℂ) := by
    simp_rw [paperFT_weilTest_self_ofReal hcont hfc, ← Complex.ofReal_mul]
    exact integral_complex_ofReal
  have hfac : (1/(2*(Real.pi:ℂ)):ℂ) = ((1/(2*Real.pi):ℝ):ℂ) := by push_cast; rfl
  have harch : weilArchRe (EF.weilTest f f) =
      (paperFT (EF.weilTest f f) (I/2)+paperFT (EF.weilTest f f) (-I/2)).re +
        (1/(2*Real.pi))*∫ t : ℝ, ‖paperFT f (t:ℂ)‖^2*EF.gammaBracket t := by
    unfold weilArchRe
    rw [hG, hfac, ← Complex.ofReal_mul, Complex.add_re, Complex.ofReal_re]
  have hg := gramPacket_gamma_lower N L hL c
  have hp := gramPacket_poles_lower N L hL c
  change _ ≤ weilArchRe (EF.weilTest f f)
  rw [harch]
  dsimp [f]
  simp only [Complex.add_re] at hp
  nlinarith

/-- An explicit coefficient-independent logarithmic lower bound. -/
theorem gramPacket_log_energy_lower (N L : ℕ) (hN : 1 ≤ N) (hL : 104 ≤ L) (c : ℕ → ℂ) :
    packetMass N L * (∑ n ∈ Finset.Icc 1 N, ‖c n‖^2) * ((1/4)*Real.log N-11) ≤
      weilArchRe (EF.weilTest (gramPacket N L c) (gramPacket N L c)) := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hl : (104:ℝ) ≤ L := by exact_mod_cast hL
  have hx : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hn
  have hlog : Real.log (N:ℝ) ≤ Real.log (1+((N*L:ℕ):ℝ)/4) := by
    apply Real.log_le_log (by linarith)
    push_cast
    nlinarith [mul_nonneg (show (0:ℝ) ≤ N by positivity) (show (0:ℝ) ≤ L-4 by linarith)]
  have hs : Real.sqrt (1+Real.log (N:ℝ)) ≤ 1+Real.log (N:ℝ)/2 := by
    have hh := Real.sq_sqrt (show 0 ≤ 1+Real.log (N:ℝ) by linarith)
    nlinarith [sq_nonneg (Real.sqrt (1+Real.log (N:ℝ))-1)]
  have hfrac : 2/(L:ℝ) ≤ 1/2 := (div_le_iff₀ (by linarith)).2 (by linarith)
  have hprod := mul_le_mul_of_nonneg_right hfrac (Real.sqrt_nonneg (1+Real.log (N:ℝ)))
  have hfloor : (1/4)*Real.log (N:ℝ)-11 ≤
      (1/2)*Real.log (1+((N*L:ℕ):ℝ)/4)-10-(2/(L:ℝ))*Real.sqrt (1+Real.log (N:ℝ)) := by
    linarith
  exact (mul_le_mul_of_nonneg_left hfloor
    (mul_nonneg (packetMass_pos N L).le (Finset.sum_nonneg fun _ _ => sq_nonneg _))).trans
      (gramPacket_full_energy_lower N L hL c)

/-- Full packet energy escapes uniformly with the packet count, including arbitrary signs. -/
theorem gramPacket_uniform_energy_escape (E : ℝ) :
    ∃ K : ℕ, ∀ N : ℕ, K ≤ N → ∀ L : ℕ, 104 ≤ L → ∀ c : ℕ → ℂ,
      E*(packetMass N L * ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2) ≤
        weilArchRe (EF.weilTest (gramPacket N L c) (gramPacket N L c)) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (max 1 (Real.exp (4*(E+11))))
  refine ⟨K, fun N hN L hL c => ?_⟩
  have hKN : (K:ℝ) ≤ N := by exact_mod_cast hN
  have hn : (1:ℝ) < N := (lt_of_le_of_lt (le_max_left _ _) hK).trans_le hKN
  have hN1 : 1 ≤ N := by exact_mod_cast hn.le
  have he : Real.exp (4*(E+11)) ≤ N :=
    ((le_max_right _ _).trans hK.le).trans hKN
  have hh := Real.log_le_log (Real.exp_pos (4*(E+11))) he
  rw [Real.log_exp] at hh
  have hfloor : E ≤ (1/4)*Real.log (N:ℝ)-11 := by linarith
  have hM := mul_nonneg (packetMass_pos N L).le
    (Finset.sum_nonneg fun n (_ : n ∈ Finset.Icc 1 N) => sq_nonneg ‖c n‖)
  calc
    _ ≤ ((1/4)*Real.log (N:ℝ)-11)*(packetMass N L * ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2) :=
      mul_le_mul_of_nonneg_right hfloor hM
    _ = _ := mul_comm _ _
    _ ≤ _ := gramPacket_log_energy_lower N L hN1 hL c

end RHTower.WeilWorkPBAP
