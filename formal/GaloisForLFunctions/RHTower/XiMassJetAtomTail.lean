import GaloisForLFunctions.RHTower.XiMassJetRetreatEndpoint
import GaloisForLFunctions.RHTower.VonMangoldtRpowTail

/-!
# The jet-modified exterior tail over all integers

The prime-restricted exterior tail extends to the full von Mangoldt sum: primality entered only
through the Dirichlet weight, and Chebyshev's `ψ(x) ≤ 7x` gives the von Mangoldt tail the same clean
power decay as `θ(x) ≤ x log 4` gives the prime tail.  This is the form the atom series of the
criterion consumes, whose index runs over all prime powers.
-/

open Complex Filter Finset Set

namespace RHTower

noncomputable section

theorem norm_lseriesTerm_vonMangoldt_nat {n : ℕ} (hn : n ≠ 0) :
    ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (1 / 2 : ℂ) n‖
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hre : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by norm_num
  rw [LSeries.norm_term_eq, if_neg hn, hre]
  have hvm : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖
      = (ArithmeticFunction.vonMangoldt n : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [hvm, Real.rpow_neg (by positivity), div_eq_mul_inv]

/-- **The pointwise atom majorant from an envelope, over all integers.** -/
theorem norm_xiMassJetAtom_le {a sigma kappa u B : ℝ} {k : ℕ} {n : ℕ}
    (ha : 1 / 2 < a) (hkappa : 1 < kappa) (hu : 0 < u) (hB : 0 ≤ B)
    (hcone : Real.exp (kappa * u) < (n : ℝ))
    (henv : ‖xiMassJetIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) k ((Real.log n : ℝ) : ℂ)‖
      ≤ B * Real.exp (-(a * Real.sqrt ((Real.log n) ^ 2 - u ^ 2)))) :
    ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) k n‖
      ≤ B * Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp ((a - 1 / 2) * (kappa * u))
        * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + (a - 1 / 2)))) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hexp1 : (1 : ℝ) < Real.exp (kappa * u) := by
    have hpos : (0 : ℝ) < kappa * u := by positivity
    calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ < Real.exp (kappa * u) := Real.exp_lt_exp.2 hpos
  have hn1 : (1 : ℝ) < (n : ℝ) := lt_trans hexp1 hcone
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hn1
  have hnne : n ≠ 0 := by
    intro h
    rw [h] at hn0
    norm_num at hn0
  set h : ℝ := Real.log n with hh
  have hhpos : 0 < h := Real.log_pos hn1
  have hcone' : kappa * u ≤ h := by
    have hlog := Real.log_lt_log (Real.exp_pos (kappa * u)) hcone
    rw [Real.log_exp] at hlog
    linarith
  have hnorm : ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) k n‖
      = ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)))
        * ‖xiMassJetIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) k ((h : ℝ) : ℂ)‖ := by
    rw [xiMassJetPrimeAtom, norm_mul, norm_lseriesTerm_vonMangoldt_nat hnne]
  have hweight0 : (0 : ℝ)
      ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_pos_of_pos hn0 _).le
  have hstep : ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) k n‖
      ≤ ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)))
        * (B * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left henv hweight0
  refine hstep.trans ?_
  have hexpo := xiMassBessel_exterior_exponent_le (a := a) (kappa := kappa) (u := u) (h := h)
    ha hkappa hu.le hcone'
  have hhalf : (n : ℝ) ^ (-(1 / 2 : ℝ)) = Real.exp (-(h / 2)) := by
    rw [Real.rpow_def_of_pos hn0, ← hh]
    congr 1
    ring
  have hpow : (n : ℝ) ^ (-(1 + (a - 1 / 2))) = Real.exp (-((1 + (a - 1 / 2)) * h)) := by
    rw [Real.rpow_def_of_pos hn0, ← hh]
    congr 1
    ring
  rw [hhalf, hpow]
  have hexpprod : Real.exp (-(h / 2)) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))
      ≤ Real.exp (-(xiMassBesselConeExponent a kappa * u))
        * Real.exp ((a - 1 / 2) * (kappa * u)) * Real.exp (-((1 + (a - 1 / 2)) * h)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hvm : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  calc (ArithmeticFunction.vonMangoldt n : ℝ) * Real.exp (-(h / 2))
        * (B * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))
      = B * ((ArithmeticFunction.vonMangoldt n : ℝ) * (Real.exp (-(h / 2))
        * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))) := by ring
    _ ≤ B * ((ArithmeticFunction.vonMangoldt n : ℝ)
          * (Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp ((a - 1 / 2) * (kappa * u)) * Real.exp (-((1 + (a - 1 / 2)) * h)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpprod hvm) hB
    _ = B * Real.exp (-(xiMassBesselConeExponent a kappa * u))
          * Real.exp ((a - 1 / 2) * (kappa * u))
        * ((ArithmeticFunction.vonMangoldt n : ℝ) * Real.exp (-((1 + (a - 1 / 2)) * h))) := by
        ring

/-- **The jet-modified exterior tail over all integers, on a sub-range.** -/
theorem sum_norm_xiMassJetAtom_subset_le {a sigma kappa u B : ℝ} {k M : ℕ}
    (ha : 1 / 2 < a) (hkappa : 1 < kappa) (hu : 0 < u) (hB : 0 ≤ B) (T : Finset ℕ)
    (hT : T ⊆ (Finset.Icc 1 M).filter (fun n : ℕ => Real.exp (kappa * u) < (n : ℝ)))
    (henv : ∀ n ∈ T,
      ‖xiMassJetIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) k ((Real.log n : ℝ) : ℂ)‖
        ≤ B * Real.exp (-(a * Real.sqrt ((Real.log n) ^ 2 - u ^ 2)))) :
    ∑ n ∈ T, ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) k n‖
      ≤ B * ((2 : ℝ) ^ (a - 1 / 2) * vonMangoldtRpowTailConstant (a - 1 / 2))
        * Real.exp (-(xiMassBesselConeExponent a kappa * u)) := by
  classical
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hδ : (0 : ℝ) < a - 1 / 2 := by linarith
  set A : ℝ := B * Real.exp (-(xiMassBesselConeExponent a kappa * u))
      * Real.exp ((a - 1 / 2) * (kappa * u)) with hAdef
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; positivity
  have hterm : ∀ n ∈ T,
      ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) k n‖
        ≤ A * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + (a - 1 / 2)))) := by
    intro n hn
    obtain ⟨-, hgt⟩ := Finset.mem_filter.mp (hT hn)
    exact norm_xiMassJetAtom_le ha hkappa hu hB hgt (henv n hn)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hwiden : ∑ n ∈ T, A * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + (a - 1 / 2))))
      ≤ ∑ n ∈ (Finset.Icc 1 M).filter (fun n : ℕ => Real.exp (kappa * u) < (n : ℝ)),
          A * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + (a - 1 / 2)))) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hT (fun n hnmem _ => ?_)
    obtain ⟨hnIcc, -⟩ := Finset.mem_filter.mp hnmem
    obtain ⟨hn1, -⟩ := Finset.mem_Icc.mp hnIcc
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hvm : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + (a - 1 / 2))) := (Real.rpow_pos_of_pos hn0 _).le
    exact mul_nonneg hA0 (mul_nonneg hvm hpow)
  refine le_trans hwiden ?_
  rw [← Finset.mul_sum]
  have hX : (1 : ℝ) ≤ Real.exp (kappa * u) := Real.one_le_exp (by positivity)
  have htail := sum_vonMangoldt_rpow_tail_le (δ := a - 1 / 2) (X := Real.exp (kappa * u)) hδ hX M
  have hstep := mul_le_mul_of_nonneg_left htail hA0
  refine hstep.trans (le_of_eq ?_)
  have hXpow : (Real.exp (kappa * u)) ^ (-(a - 1 / 2))
      = Real.exp (-((a - 1 / 2) * (kappa * u))) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  rw [hXpow, hAdef]
  have hcancel : Real.exp ((a - 1 / 2) * (kappa * u)) * Real.exp (-((a - 1 / 2) * (kappa * u)))
      = 1 := by
    rw [← Real.exp_add]
    simp
  calc (B * Real.exp (-(xiMassBesselConeExponent a kappa * u))
        * Real.exp ((a - 1 / 2) * (kappa * u)))
      * ((2 : ℝ) ^ (a - 1 / 2) * vonMangoldtRpowTailConstant (a - 1 / 2)
        * Real.exp (-((a - 1 / 2) * (kappa * u))))
      = (B * ((2 : ℝ) ^ (a - 1 / 2) * vonMangoldtRpowTailConstant (a - 1 / 2))
          * Real.exp (-(xiMassBesselConeExponent a kappa * u)))
        * (Real.exp ((a - 1 / 2) * (kappa * u))
          * Real.exp (-((a - 1 / 2) * (kappa * u)))) := by ring
    _ = B * ((2 : ℝ) ^ (a - 1 / 2) * vonMangoldtRpowTailConstant (a - 1 / 2))
        * Real.exp (-(xiMassBesselConeExponent a kappa * u)) := by rw [hcancel, mul_one]

set_option maxHeartbeats 1000000 in
/-- **(22.8)/(22.10)/(22.11), all-integer form.**  For every jet order the whole exterior von
Mangoldt tail past `κ_B u − q_n log u` is bounded by a constant, uniformly in the height and in the
truncation. -/
theorem exists_bound_xiMassJetAtomTail_endpoint {a sigma : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (n : ℕ) :
    ∃ C u₀ : ℝ, 0 < C ∧ 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ M : ℕ,
      ∑ p ∈ (Finset.Icc 1 M).filter (fun p : ℕ =>
          Real.exp (xiMassSpacelikeSharpSlope a * u
            - xiMassJetRetreatCoeff a n * Real.log u) < (p : ℝ)),
        ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖ ≤ C := by
  classical
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hδ : (0 : ℝ) < a - 1 / 2 := by linarith
  have hm : (0 : ℝ) < 2 * a ^ 2 - 1 / 2 := by nlinarith
  set Cp : ℝ := (2 : ℝ) ^ (a - 1 / 2) * vonMangoldtRpowTailConstant (a - 1 / 2) with hCpdef
  have hCp0 : (0 : ℝ) ≤ Cp := by
    rw [hCpdef]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (vonMangoldtRpowTailConstant_nonneg hδ)
  set κ : ℝ := xiMassSpacelikeSharpSlope a with hκdef
  have hκ1 : 1 < κ := by rw [hκdef]; exact one_lt_xiMassSpacelikeSharpSlope ha
  set q : ℝ := xiMassJetRetreatCoeff a n with hqdef
  have hq0 : 0 < q := by rw [hqdef]; exact xiMassJetRetreatCoeff_pos ha n
  have hqm : (2 * a ^ 2 - 1 / 2) * q = ((n : ℝ) + 1) / 2 := by
    rw [hqdef]; exact xiMassJetRetreatCoeff_mul ha n
  obtain ⟨Cw, uw, hCw, huw0, hwin⟩ := exists_norm_xiMassJetIterate_window_le' ha hsigma n
  obtain ⟨Cf, uf, hCf, huf0, hfar⟩ := exists_norm_xiMassJetIterate_far_le ha hsigma n
  obtain ⟨ua, hua0, hact⟩ := exists_logRetreat_data ha hq0
  have hgrow4 : Tendsto (fun u : ℝ => u ^ ((1 : ℝ) / 4)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  obtain ⟨ub, hub⟩ := (hgrow4.eventually_ge_atTop (8 * q)).exists_forall_of_atTop
  refine ⟨|Cw * Cp * Real.exp 1| + |Cf * Cp| + 1,
    max uw (max uf (max ua (max ub (max 1 (xiMassFarThreshold a))))), by positivity,
    lt_of_lt_of_le one_pos (by simp), ?_⟩
  intro u hu M
  have huw : uw ≤ u := le_trans (le_max_left _ _) hu
  have huf : uf ≤ u := le_trans (by simp) hu
  have hua : ua ≤ u := le_trans (by simp) hu
  have hub' : ub ≤ u := le_trans (by simp) hu
  have hu1 : (1 : ℝ) ≤ u := le_trans (by simp) hu
  have hfth : xiMassFarThreshold a ≤ u := le_trans (by simp) hu
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
  have hlog0 : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
  obtain ⟨hcone, haction⟩ := hact u hua
  rw [← hκdef] at hcone haction
  set H : ℝ := κ * u - q * Real.log u with hHdef
  have hHu : u < H := by nlinarith [hcone]
  have hHpos : (0 : ℝ) < H := lt_trans hu0 hHu
  have hsq : Real.sqrt u = u ^ ((1 : ℝ) / 4) * u ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hu0]
    norm_num
  have hp4 : (0 : ℝ) < u ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hu0 _
  have hwidth : q * Real.log u ≤ Real.sqrt u / 2 := by
    have h4 := log_le_four_mul_rpow hu0
    have h8 := hub u hub'
    rw [hsq]
    nlinarith [mul_le_mul_of_nonneg_left h4 hq0.le, mul_le_mul_of_nonneg_right h8 hp4.le]
  have hS : (0 : ℝ) < Real.sqrt u ^ (n + 1) := pow_pos (Real.sqrt_pos.2 hu0) _
  have hpow : Real.exp (((n : ℝ) + 1) / 2 * Real.log u) = Real.sqrt u ^ (n + 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (u ^ ((1 : ℝ) / 2)) (n + 1),
      ← Real.rpow_mul hu0.le, Real.rpow_def_of_pos hu0]
    congr 1
    push_cast
    ring
  set T : Finset ℕ := (Finset.Icc 1 M).filter
    (fun p : ℕ => Real.exp H < (p : ℝ)) with hTdef
  have hboundA : ∑ p ∈ T.filter (fun p : ℕ => (p : ℝ) ≤ Real.exp (κ * u)),
      ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
      ≤ Cw / Real.sqrt u ^ (n + 1) * Cp
        * Real.exp (-(xiMassBesselConeExponent a (H / u) * u)) := by
    have hkapA : 1 < H / u := (one_lt_div hu0).2 hHu
    refine sum_norm_xiMassJetAtom_subset_le (a := a) (sigma := sigma) (kappa := H / u)
      (u := u) (B := Cw / Real.sqrt u ^ (n + 1)) (k := n) (M := M) ha hkapA hu0
      (by positivity) _ ?_ ?_
    · intro p hp
      have hpT := (Finset.mem_filter.mp hp).1
      rw [hTdef] at hpT
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpT).1, ?_⟩
      rw [div_mul_cancel₀ H hu0.ne']
      exact (Finset.mem_filter.mp hpT).2
    · intro p hp
      obtain ⟨hpT0, hple⟩ := Finset.mem_filter.mp hp
      have hpT := hpT0
      rw [hTdef] at hpT
      obtain ⟨hpIcc, hgt⟩ := Finset.mem_filter.mp hpT
      obtain ⟨hp1, -⟩ := Finset.mem_Icc.mp hpIcc
      have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
      have hplow : H < Real.log p := by
        have h := Real.log_lt_log (Real.exp_pos H) hgt
        rwa [Real.log_exp] at h
      have hplow' : κ * u - q * Real.log u < Real.log p := by rw [← hHdef]; exact hplow
      have hphigh : Real.log p ≤ κ * u := (Real.log_le_iff_le_exp hppos).2 hple
      set t : ℝ := Real.log p - κ * u with htdef
      have habs : |t| ≤ Real.sqrt u / 2 := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · rw [htdef]; linarith
        · rw [htdef]; linarith [Real.sqrt_nonneg u]
      have hb := hwin u huw t habs
      have hteq : xiMassSpacelikeSharpSlope a * u + t = Real.log p := by
        rw [← hκdef, htdef]; ring
      rw [hteq] at hb
      exact hb
  have hboundB : ∑ p ∈ T.filter (fun p : ℕ => ¬ ((p : ℝ) ≤ Real.exp (κ * u))),
      ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
      ≤ Cf * Cp * Real.exp (-(xiMassBesselConeExponent a κ * u)) := by
    refine sum_norm_xiMassJetAtom_subset_le (a := a) (sigma := sigma) (kappa := κ)
      (u := u) (B := Cf) (k := n) (M := M) ha hκ1 hu0 hCf.le _ ?_ ?_
    · intro p hp
      obtain ⟨hpT0, hgt⟩ := Finset.mem_filter.mp hp
      have hpT := hpT0
      rw [hTdef] at hpT
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpT).1, not_le.mp hgt⟩
    · intro p hp
      obtain ⟨hpT0, hgt⟩ := Finset.mem_filter.mp hp
      have hpT := hpT0
      rw [hTdef] at hpT
      have hplow : κ * u < Real.log p := by
        have h := Real.log_lt_log (Real.exp_pos (κ * u)) (not_le.mp hgt)
        rwa [Real.log_exp] at h
      have hku : u ≤ κ * u := by nlinarith
      exact hfar u huf (Real.log p) (by rw [← hκdef]; linarith) (by linarith)
  have hAexp : Real.exp (-(xiMassBesselConeExponent a (H / u) * u))
      ≤ Real.exp 1 * Real.sqrt u ^ (n + 1) := by
    have hmov := xiMassBesselConeExponent_movingSlope (a := a) (u := u) (H := H) hu0 hHu.le
    rw [hmov]
    have heq : -(a * Real.sqrt (H ^ 2 - u ^ 2) - H / 2)
        = H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2) := by ring
    rw [heq]
    have hact2 : H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)
        ≤ ((n : ℝ) + 1) / 2 * Real.log u + 1 := by
      refine haction.trans ?_
      have hid : (2 * a ^ 2 - 1 / 2) * (q * Real.log u) = ((n : ℝ) + 1) / 2 * Real.log u := by
        rw [← hqm]; ring
      linarith [hid]
    calc Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2))
        ≤ Real.exp (((n : ℝ) + 1) / 2 * Real.log u + 1) := Real.exp_le_exp.2 hact2
      _ = Real.exp (((n : ℝ) + 1) / 2 * Real.log u) * Real.exp 1 := Real.exp_add _ _
      _ = Real.sqrt u ^ (n + 1) * Real.exp 1 := by rw [hpow]
      _ = Real.exp 1 * Real.sqrt u ^ (n + 1) := by ring
  have hBexp : Real.exp (-(xiMassBesselConeExponent a κ * u)) = 1 := by
    rw [hκdef, xiMassBesselConeExponent_sharpSlope_eq_zero ha]
    simp
  calc ∑ p ∈ T, ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
      = ∑ p ∈ T.filter (fun p : ℕ => (p : ℝ) ≤ Real.exp (κ * u)),
            ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖
          + ∑ p ∈ T.filter (fun p : ℕ => ¬ ((p : ℝ) ≤ Real.exp (κ * u))),
            ‖xiMassJetPrimeAtom a ((sigma : ℂ) + (u : ℂ) * Complex.I) n p‖ :=
        (Finset.sum_filter_add_sum_filter_not T _ _).symm
    _ ≤ Cw / Real.sqrt u ^ (n + 1) * Cp * (Real.exp 1 * Real.sqrt u ^ (n + 1))
          + Cf * Cp * 1 := by
        refine add_le_add (hboundA.trans ?_) (hboundB.trans ?_)
        · exact mul_le_mul_of_nonneg_left hAexp
            (mul_nonneg (div_nonneg hCw.le hS.le) hCp0)
        · rw [hBexp]
    _ = Cw * Cp * Real.exp 1 + Cf * Cp := by field_simp
    _ ≤ |Cw * Cp * Real.exp 1| + |Cf * Cp| + 1 := by
        linarith [le_abs_self (Cw * Cp * Real.exp 1), le_abs_self (Cf * Cp)]

end

end RHTower
