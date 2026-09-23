import GaloisForLFunctions.RHTower.LiEvenCrossInfiniteCriticalAmplitudeSchattenBoundaryNoGo
import GaloisForLFunctions.RHTower.XiOrderedPrimeApproximationAsymptotics

/-!
# Infinite critical-current uniform-tail no-go

The multiplicity-ordered positive Xi ordinates force coherent endpoint-current blocks.
For every critical-copy enumeration with those ordinates, cofinal dyadic shells admit a
resonant integer Li mode whose normalized current stays above one fixed positive constant.
Consequently no such enumeration has uniformly Cauchy normalized endpoint-current tails.

This closes the LI route's proposed finite-prefix-to-full-packet passage: finite critical-packet
sign excursions cannot be transported to the full critical packet through uniform tail control.
-/

open Filter
open scoped BigOperators

namespace RHTower

noncomputable section

def liEvenCrossRVMScale (n : ℕ) : ℝ :=
  2 * Real.pi * ((n : ℝ) + 1) / Real.log ((n : ℝ) + 1)

theorem tendsto_xiOrderedPositiveOrdinate_div_liEvenCrossRVMScale :
    Tendsto (fun n : ℕ =>
      xiOrderedPositiveOrdinate n / liEvenCrossRVMScale n)
      atTop (nhds 1) := by
  have h := tendsto_routeKRVMQuantile_div_rvmModel.div
    tendsto_routeKRVMQuantile_div_xiOrderedPositiveOrdinate
    (by norm_num : (1 : ℝ) ≠ 0)
  have h' : Tendsto
      ((fun n : ℕ => routeKRVMQuantile n /
          (2 * Real.pi * ((n : ℝ) + 1) / Real.log ((n : ℝ) + 1))) /
        (fun n : ℕ => routeKRVMQuantile n / xiOrderedPositiveOrdinate n))
      atTop (nhds 1) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hgamma : xiOrderedPositiveOrdinate n ≠ 0 :=
    (xiOrderedPositiveOrdinate_pos n).ne'
  have hroute : routeKRVMQuantile n ≠ 0 :=
    (routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)).ne'
  have hlog : Real.log ((n : ℝ) + 1) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hn))
  change
    (routeKRVMQuantile n /
        (2 * Real.pi * ((n : ℝ) + 1) / Real.log ((n : ℝ) + 1))) /
      (routeKRVMQuantile n / xiOrderedPositiveOrdinate n) =
    xiOrderedPositiveOrdinate n / liEvenCrossRVMScale n
  simp only [liEvenCrossRVMScale]
  field_simp [hgamma, hroute, hlog, Real.pi_ne_zero]

theorem liEvenCrossRVMScale_pos {n : ℕ} (hn : 0 < n) :
    0 < liEvenCrossRVMScale n := by
  rw [liEvenCrossRVMScale]
  have hlog : 0 < Real.log ((n : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hn)
  positivity

theorem liEvenCrossRVMScale_two_mul_le (n : ℕ) (hn : 0 < n) :
    liEvenCrossRVMScale (2 * n) ≤ 2 * liEvenCrossRVMScale n := by
  have hlogn : 0 < Real.log ((n : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast Nat.succ_lt_succ hn)
  have harg : (n : ℝ) + 1 ≤ ((2 * n : ℕ) : ℝ) + 1 := by
    norm_num
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    linarith
  have hlogle : Real.log ((n : ℝ) + 1) ≤
      Real.log (((2 * n : ℕ) : ℝ) + 1) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by show 0 < (n : ℝ) + 1; positivity)
      (by show 0 < ((2 * n : ℕ) : ℝ) + 1; positivity) harg
  have hlog2 : 0 < Real.log (((2 * n : ℕ) : ℝ) + 1) :=
    hlogn.trans_le hlogle
  rw [liEvenCrossRVMScale, liEvenCrossRVMScale]
  calc
    2 * Real.pi * (((2 * n : ℕ) : ℝ) + 1) /
        Real.log (((2 * n : ℕ) : ℝ) + 1) ≤
        2 * Real.pi * (2 * ((n : ℝ) + 1)) /
          Real.log ((n : ℝ) + 1) := by
      gcongr
      · norm_num
        have hn0 : 0 ≤ (n : ℝ) := by positivity
        linarith
    _ = 2 * (2 * Real.pi * ((n : ℝ) + 1) /
          Real.log ((n : ℝ) + 1)) := by ring

theorem eventually_xiOrderedPositiveOrdinate_two_mul_le_eight_mul :
    ∀ᶠ n : ℕ in atTop,
      xiOrderedPositiveOrdinate (2 * n) ≤
        8 * xiOrderedPositiveOrdinate n := by
  have hb : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) < xiOrderedPositiveOrdinate n / liEvenCrossRVMScale n ∧
      xiOrderedPositiveOrdinate n / liEvenCrossRVMScale n < 2 :=
    tendsto_xiOrderedPositiveOrdinate_div_liEvenCrossRVMScale.eventually
      (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2))
  rw [eventually_atTop] at hb
  obtain ⟨N, hN⟩ := hb
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have h2nN : N ≤ 2 * n := by omega
  have hnBounds := hN n hnN
  have h2nBounds := hN (2 * n) h2nN
  have hmodeln : 0 < liEvenCrossRVMScale n :=
    liEvenCrossRVMScale_pos (by omega)
  have hmodel2n : 0 < liEvenCrossRVMScale (2 * n) :=
    liEvenCrossRVMScale_pos (by omega)
  have hgammaLower : liEvenCrossRVMScale n <
      2 * xiOrderedPositiveOrdinate n := by
    have h := hnBounds.1
    rw [lt_div_iff₀ hmodeln] at h
    nlinarith
  have hgammaUpper : xiOrderedPositiveOrdinate (2 * n) <
      2 * liEvenCrossRVMScale (2 * n) := by
    have h := h2nBounds.2
    rw [div_lt_iff₀ hmodel2n] at h
    exact h
  have hmodelDouble := liEvenCrossRVMScale_two_mul_le n (by omega)
  nlinarith

theorem exists_eventually_xiOrderedPositiveOrdinate_le_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      xiOrderedPositiveOrdinate n ≤ C * ((n : ℝ) + 1) := by
  obtain ⟨D, hD, hdist⟩ :=
    exists_eventually_abs_xiOrderedPositiveOrdinate_sub_routeKRVMQuantile_le
  let A : ℝ := 2 * routeKRVMBase * Real.exp 1
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (mul_pos two_pos routeKRVMBase_pos) (Real.exp_pos 1)
  refine ⟨A + D, by linarith, ?_⟩
  filter_upwards [hdist] with n hn
  have hroute := routeKRVMQuantile_le_linear n
  have hdiff : xiOrderedPositiveOrdinate n - routeKRVMQuantile n ≤ D :=
    (abs_le.mp hn).2
  have hsucc : 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  dsimp [A]
  nlinarith [mul_le_mul_of_nonneg_left hsucc hD.le]

theorem liEvenCrossCriticalAtomAmplitude_oneFourth_eq_sin_half_frequency
    (q : XiCriticalLineResolventCopy)
    (him : 0 < (q.1.1 : ℂ).im) :
    liEvenCrossCriticalAtomAmplitude (1 / 4) q =
      Real.sin (liEvenCrossCriticalAtomFrequency (1 / 4) q / 2) := by
  set gamma : ℝ := (q.1.1 : ℂ).im with hgamma
  set den : ℝ := gamma ^ (2 : ℕ) + 1 / 4 with hden
  have hgammaPos : 0 < gamma := by simpa [hgamma] using him
  have hdenPos : 0 < den := by dsimp [den]; positivity
  have hmass : liEvenCrossCriticalAtomMass (1 / 4) q = 1 / den := by
    simpa [hgamma, hden, add_comm] using
      liEvenCrossCriticalAtomMass_eq_imaginary (v := 1 / 4) (by norm_num) q
  have hnode : liEvenCrossCriticalAtomNode (1 / 4) q = (1 / 4) / den := by
    rw [liEvenCrossCriticalAtomNode, hmass]
    ring
  have hcos := liEvenCrossCriticalAtomAngle_cos
    (v := 1 / 4) (by norm_num) (by norm_num) q
  have hcos' : Real.cos (liEvenCrossCriticalAtomAngle (1 / 4) q) =
      (1 / 4 - gamma ^ (2 : ℕ)) / den := by
    rw [hcos, hnode]
    dsimp [den]
    field_simp
    ring
  obtain ⟨hthetaHalf, hthetaPi⟩ := liEvenCrossCriticalAtomAngle_mem
    (v := 1 / 4) (by norm_num) (by norm_num) q
  have hsinPos : 0 < Real.sin (liEvenCrossCriticalAtomAngle (1 / 4) q) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) hthetaPi
  have htrig := Real.sin_sq_add_cos_sq
    (liEvenCrossCriticalAtomAngle (1 / 4) q)
  have hsinSq :
      Real.sin (liEvenCrossCriticalAtomAngle (1 / 4) q) ^ (2 : ℕ) =
        (gamma / den) ^ (2 : ℕ) := by
    rw [hcos'] at htrig
    field_simp [hdenPos.ne'] at htrig ⊢
    nlinarith
  have hsin : Real.sin (liEvenCrossCriticalAtomAngle (1 / 4) q) =
      gamma / den := by
    have hrightPos : 0 < gamma / den := div_pos hgammaPos hdenPos
    nlinarith
  rw [liEvenCrossCriticalAtomAmplitude_oneFourth_eq_imaginary q him]
  rw [liEvenCrossCriticalAtomFrequency]
  rw [show (2 * Real.pi - 2 * liEvenCrossCriticalAtomAngle (1 / 4) q) / 2 =
      Real.pi - liEvenCrossCriticalAtomAngle (1 / 4) q by ring]
  rw [Real.sin_pi_sub, hsin]

theorem two_mul_liEvenCrossCriticalAtomAmplitude_oneFourth_le_frequency
    (q : XiCriticalLineResolventCopy)
    (him : 0 < (q.1.1 : ℂ).im) :
    2 * liEvenCrossCriticalAtomAmplitude (1 / 4) q ≤
      liEvenCrossCriticalAtomFrequency (1 / 4) q := by
  have hfreq := liEvenCrossCriticalAtomFrequency_mem
    (v := 1 / 4) (by norm_num) (by norm_num) q
  have hhalf : 0 ≤ liEvenCrossCriticalAtomFrequency (1 / 4) q / 2 := by
    linarith
  have hsin := Real.sin_le hhalf
  rw [← liEvenCrossCriticalAtomAmplitude_oneFourth_eq_sin_half_frequency q him] at hsin
  linarith

theorem liEvenCrossCriticalAtomFrequency_oneFourth_le_pi_mul_amplitude
    (q : XiCriticalLineResolventCopy)
    (him : 0 < (q.1.1 : ℂ).im) :
    liEvenCrossCriticalAtomFrequency (1 / 4) q ≤
      Real.pi * liEvenCrossCriticalAtomAmplitude (1 / 4) q := by
  have hfreq := liEvenCrossCriticalAtomFrequency_mem
    (v := 1 / 4) (by norm_num) (by norm_num) q
  have hhalf0 : 0 ≤ liEvenCrossCriticalAtomFrequency (1 / 4) q / 2 := by
    linarith
  have hhalfpi : liEvenCrossCriticalAtomFrequency (1 / 4) q / 2 ≤
      Real.pi / 2 := by linarith
  have hsin := Real.mul_le_sin hhalf0 hhalfpi
  rw [← liEvenCrossCriticalAtomAmplitude_oneFourth_eq_sin_half_frequency q him] at hsin
  have hpi : 0 < Real.pi := Real.pi_pos
  calc
    liEvenCrossCriticalAtomFrequency (1 / 4) q =
        Real.pi * (2 / Real.pi *
          (liEvenCrossCriticalAtomFrequency (1 / 4) q / 2)) := by
      field_simp [hpi.ne']
    _ ≤ Real.pi * liEvenCrossCriticalAtomAmplitude (1 / 4) q := by
      gcongr

def liEvenCrossFullCriticalNormalizedTail
    (q : ℕ → XiCriticalLineResolventCopy) (L M k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico L M,
    liEvenCrossCriticalAtomAmplitude (1 / 4) (q j) *
      Real.sin ((k : ℝ) * liEvenCrossCriticalAtomFrequency (1 / 4) (q j))

def LiEvenCrossFullCriticalNormalizedUniformCauchy
    (q : ℕ → XiCriticalLineResolventCopy) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ L M k : ℕ,
    N ≤ L → L ≤ M →
      |liEvenCrossFullCriticalNormalizedTail q L M k| < ε

def liEvenCrossOrderedEndpointResonantMode (L : ℕ) : ℕ :=
  ⌈(64 * liEvenCrossOrderedEndpointAmplitude L)⁻¹⌉₊

theorem liEvenCrossOrderedEndpointResonantMode_lower (L : ℕ) :
    (64 * liEvenCrossOrderedEndpointAmplitude L)⁻¹ ≤
      (liEvenCrossOrderedEndpointResonantMode L : ℝ) := by
  exact Nat.le_ceil _

theorem liEvenCrossOrderedEndpointResonantMode_upper
    {L : ℕ} (hgamma : 64 ≤ xiOrderedPositiveOrdinate L) :
    (liEvenCrossOrderedEndpointResonantMode L : ℝ) ≤
      2 * (64 * liEvenCrossOrderedEndpointAmplitude L)⁻¹ := by
  set a := liEvenCrossOrderedEndpointAmplitude L with ha
  have haPos : 0 < a := by simpa [ha] using liEvenCrossOrderedEndpointAmplitude_pos L
  have haUpper : a ≤ (xiOrderedPositiveOrdinate L)⁻¹ := by
    simpa [ha] using liEvenCrossOrderedEndpointAmplitude_le_inv L
  have hgammaPos : 0 < xiOrderedPositiveOrdinate L :=
    xiOrderedPositiveOrdinate_pos L
  have h64a : 64 * a ≤ 1 := by
    calc
      64 * a ≤ 64 * (xiOrderedPositiveOrdinate L)⁻¹ := by gcongr
      _ ≤ 1 := by
        rw [inv_eq_one_div, mul_one_div, div_le_iff₀ hgammaPos]
        simpa using hgamma
  have hxOne : 1 ≤ (64 * a)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by positivity : 0 < 64 * a)]
    simpa using h64a
  have hceil := Nat.ceil_lt_add_one (inv_nonneg.mpr (by positivity : 0 ≤ 64 * a))
  change (liEvenCrossOrderedEndpointResonantMode L : ℝ) ≤ 2 * (64 * a)⁻¹
  rw [liEvenCrossOrderedEndpointResonantMode, ← ha]
  exact le_trans hceil.le (by nlinarith)

theorem liEvenCrossFullCriticalNormalizedTail_dyadic_term_lower
    (q : ℕ → XiCriticalLineResolventCopy)
    (hordinate : ∀ n : ℕ,
      ((q n).1.1 : ℂ).im = xiOrderedPositiveOrdinate n)
    {L j : ℕ} (hgamma : 64 ≤ xiOrderedPositiveOrdinate L)
    (hj : j ∈ Finset.Ico L (2 * L)) :
    (4 / Real.pi) *
        (64 * liEvenCrossOrderedEndpointAmplitude L)⁻¹ *
        ((xiOrderedPositiveOrdinate (2 * L))⁻¹ / 2) ^ (2 : ℕ) ≤
      liEvenCrossCriticalAtomAmplitude (1 / 4) (q j) *
        Real.sin ((liEvenCrossOrderedEndpointResonantMode L : ℝ) *
          liEvenCrossCriticalAtomFrequency (1 / 4) (q j)) := by
  set aL := liEvenCrossOrderedEndpointAmplitude L with haL
  set aj := liEvenCrossOrderedEndpointAmplitude j with haj
  set gammaL := xiOrderedPositiveOrdinate L with hgammaL
  set gammaj := xiOrderedPositiveOrdinate j with hgammaj
  set gamma2 := xiOrderedPositiveOrdinate (2 * L) with hgamma2
  set omega := liEvenCrossCriticalAtomFrequency (1 / 4) (q j) with homega
  set k : ℝ := (liEvenCrossOrderedEndpointResonantMode L : ℝ) with hk
  set x : ℝ := (64 * aL)⁻¹ with hx
  have haLPos : 0 < aL := by simpa [haL] using
    (liEvenCrossOrderedEndpointAmplitude_pos L)
  have hajPos : 0 < aj := by simpa [haj] using
    (liEvenCrossOrderedEndpointAmplitude_pos j)
  have hgammaLPos : 0 < gammaL := by simpa [hgammaL] using
    (xiOrderedPositiveOrdinate_pos L)
  have hgammajPos : 0 < gammaj := by simpa [hgammaj] using
    (xiOrderedPositiveOrdinate_pos j)
  have hgamma2Pos : 0 < gamma2 := by simpa [hgamma2] using
    (xiOrderedPositiveOrdinate_pos (2 * L))
  have himj : 0 < ((q j).1.1 : ℂ).im := by
    rw [hordinate j]
    exact xiOrderedPositiveOrdinate_pos j
  have hatom : liEvenCrossCriticalAtomAmplitude (1 / 4) (q j) = aj := by
    rw [liEvenCrossCriticalAtomAmplitude_oneFourth_eq_imaginary (q j) himj,
      hordinate j]
    rfl
  have hLj : L ≤ j := (Finset.mem_Ico.mp hj).1
  have hj2 : j ≤ 2 * L := (Finset.mem_Ico.mp hj).2.le
  have hgammaLj : gammaL ≤ gammaj := by
    simpa [hgammaL, hgammaj] using xiOrderedPositiveOrdinate_monotone hLj
  have hgammaj2 : gammaj ≤ gamma2 := by
    simpa [hgammaj, hgamma2] using xiOrderedPositiveOrdinate_monotone hj2
  have hajUpperInv : aj ≤ gammaj⁻¹ := by
    simpa [haj, hgammaj] using liEvenCrossOrderedEndpointAmplitude_le_inv j
  have hinvGammajLe : gammaj⁻¹ ≤ gammaL⁻¹ :=
    (inv_le_inv₀ hgammajPos hgammaLPos).2 hgammaLj
  have hinvGammaLLe : gammaL⁻¹ ≤ 2 * aL := by
    simpa [haL, hgammaL] using
      inv_le_two_mul_liEvenCrossOrderedEndpointAmplitude L
  have hajUpper : aj ≤ 2 * aL :=
    hajUpperInv.trans (hinvGammajLe.trans hinvGammaLLe)
  have homegaPos : 0 < omega := by
    simpa [homega] using (liEvenCrossCriticalAtomFrequency_mem
      (v := 1 / 4) (by norm_num) (by norm_num) (q j)).1
  have homegaUpper : omega ≤ Real.pi * aj := by
    rw [homega]
    calc
      liEvenCrossCriticalAtomFrequency (1 / 4) (q j) ≤
          Real.pi * liEvenCrossCriticalAtomAmplitude (1 / 4) (q j) :=
        liEvenCrossCriticalAtomFrequency_oneFourth_le_pi_mul_amplitude (q j) himj
      _ = Real.pi * aj := by rw [hatom]
  have homegaUpperL : omega ≤ 2 * Real.pi * aL := by
    calc
      omega ≤ Real.pi * aj := homegaUpper
      _ ≤ Real.pi * (2 * aL) := by gcongr
      _ = 2 * Real.pi * aL := by ring
  have hxPos : 0 < x := by dsimp [x]; positivity
  have hkLower : x ≤ k := by
    simpa [x, aL, k] using liEvenCrossOrderedEndpointResonantMode_lower L
  have hkUpper : k ≤ 2 * x := by
    simpa [x, aL, k, gammaL] using
      liEvenCrossOrderedEndpointResonantMode_upper (L := L) hgamma
  have hphase0 : 0 ≤ k * omega := mul_nonneg (by positivity) homegaPos.le
  have hphaseUpper : k * omega ≤ Real.pi / 16 := by
    calc
      k * omega ≤ (2 * x) * (2 * Real.pi * aL) :=
        mul_le_mul hkUpper homegaUpperL homegaPos.le (by positivity)
      _ = Real.pi / 16 := by
        dsimp [x]
        field_simp [haLPos.ne', Real.pi_ne_zero]
        ring
  have hsin := Real.mul_le_sin hphase0
    (hphaseUpper.trans (by nlinarith [Real.pi_pos] : Real.pi / 16 ≤ Real.pi / 2))
  have homegaLower : 2 * aj ≤ omega := by
    rw [homega]
    calc
      2 * aj = 2 * liEvenCrossCriticalAtomAmplitude (1 / 4) (q j) := by rw [hatom]
      _ ≤ liEvenCrossCriticalAtomFrequency (1 / 4) (q j) :=
        two_mul_liEvenCrossCriticalAtomAmplitude_oneFourth_le_frequency (q j) himj
  have hphaseLower : 2 * x * aj ≤ k * omega := by
    calc
      2 * x * aj = x * (2 * aj) := by ring
      _ ≤ x * omega := mul_le_mul_of_nonneg_left homegaLower hxPos.le
      _ ≤ k * omega := mul_le_mul_of_nonneg_right hkLower homegaPos.le
  have hsinLower : (4 / Real.pi) * x * aj ≤ Real.sin (k * omega) := by
    calc
      (4 / Real.pi) * x * aj = (2 / Real.pi) * (2 * x * aj) := by ring
      _ ≤ (2 / Real.pi) * (k * omega) := by gcongr
      _ ≤ Real.sin (k * omega) := hsin
  have hinv2Le : gamma2⁻¹ ≤ gammaj⁻¹ :=
    (inv_le_inv₀ hgamma2Pos hgammajPos).2 hgammaj2
  have hinvGammajAmp : gammaj⁻¹ ≤ 2 * aj := by
    simpa [haj, hgammaj] using
      inv_le_two_mul_liEvenCrossOrderedEndpointAmplitude j
  have haLower : gamma2⁻¹ / 2 ≤ aj := by
    nlinarith [hinv2Le.trans hinvGammajAmp]
  have haLowerSq : (gamma2⁻¹ / 2) ^ (2 : ℕ) ≤ aj ^ (2 : ℕ) := by
    have hleft : 0 ≤ gamma2⁻¹ / 2 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr haLower) (add_nonneg hajPos.le hleft)]
  calc
    (4 / Real.pi) *
        (64 * liEvenCrossOrderedEndpointAmplitude L)⁻¹ *
        ((xiOrderedPositiveOrdinate (2 * L))⁻¹ / 2) ^ (2 : ℕ) =
        (4 / Real.pi) * x * (gamma2⁻¹ / 2) ^ (2 : ℕ) := by
      simp only [x, aL, gamma2]
    _ ≤ (4 / Real.pi) * x * aj ^ (2 : ℕ) := by gcongr
    _ = aj * ((4 / Real.pi) * x * aj) := by ring
    _ ≤ aj * Real.sin (k * omega) :=
      mul_le_mul_of_nonneg_left hsinLower hajPos.le
    _ = liEvenCrossCriticalAtomAmplitude (1 / 4) (q j) *
        Real.sin ((liEvenCrossOrderedEndpointResonantMode L : ℝ) *
          liEvenCrossCriticalAtomFrequency (1 / 4) (q j)) := by
      rw [hatom]

theorem liEvenCrossFullCriticalNormalizedTail_dyadic_lower
    (q : ℕ → XiCriticalLineResolventCopy)
    (hordinate : ∀ n : ℕ,
      ((q n).1.1 : ℂ).im = xiOrderedPositiveOrdinate n)
    {L : ℕ} (hgamma : 64 ≤ xiOrderedPositiveOrdinate L) :
    (L : ℝ) * ((4 / Real.pi) *
        (64 * liEvenCrossOrderedEndpointAmplitude L)⁻¹ *
        ((xiOrderedPositiveOrdinate (2 * L))⁻¹ / 2) ^ (2 : ℕ)) ≤
      liEvenCrossFullCriticalNormalizedTail q L (2 * L)
        (liEvenCrossOrderedEndpointResonantMode L) := by
  rw [liEvenCrossFullCriticalNormalizedTail]
  calc
    (L : ℝ) * ((4 / Real.pi) *
        (64 * liEvenCrossOrderedEndpointAmplitude L)⁻¹ *
        ((xiOrderedPositiveOrdinate (2 * L))⁻¹ / 2) ^ (2 : ℕ)) =
      ∑ _j ∈ Finset.Ico L (2 * L),
        ((4 / Real.pi) *
          (64 * liEvenCrossOrderedEndpointAmplitude L)⁻¹ *
          ((xiOrderedPositiveOrdinate (2 * L))⁻¹ / 2) ^ (2 : ℕ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1
      norm_cast
      simp
      omega
    _ ≤ ∑ j ∈ Finset.Ico L (2 * L),
        liEvenCrossCriticalAtomAmplitude (1 / 4) (q j) *
          Real.sin ((liEvenCrossOrderedEndpointResonantMode L : ℝ) *
            liEvenCrossCriticalAtomFrequency (1 / 4) (q j)) := by
      exact Finset.sum_le_sum fun j hj =>
        liEvenCrossFullCriticalNormalizedTail_dyadic_term_lower
          q hordinate hgamma hj

theorem liEvenCrossFullCriticalNormalizedTail_dyadic_scalar_lower
    {L : ℕ} (hL : 1 ≤ L) {C : ℝ} (hC : 0 < C)
    (hlinear : xiOrderedPositiveOrdinate L ≤ C * ((L : ℝ) + 1))
    (hdyadic : xiOrderedPositiveOrdinate (2 * L) ≤
      8 * xiOrderedPositiveOrdinate L) :
    1 / (8192 * Real.pi * C) ≤
      (L : ℝ) * ((4 / Real.pi) *
        (64 * liEvenCrossOrderedEndpointAmplitude L)⁻¹ *
        ((xiOrderedPositiveOrdinate (2 * L))⁻¹ / 2) ^ (2 : ℕ)) := by
  set g := xiOrderedPositiveOrdinate L with hg
  set g2 := xiOrderedPositiveOrdinate (2 * L) with hg2
  set a := liEvenCrossOrderedEndpointAmplitude L with ha
  have hgPos : 0 < g := by
    simpa [hg] using xiOrderedPositiveOrdinate_pos L
  have hg2Pos : 0 < g2 := by
    simpa [hg2] using xiOrderedPositiveOrdinate_pos (2 * L)
  have haPos : 0 < a := by
    simpa [ha] using liEvenCrossOrderedEndpointAmplitude_pos L
  have haInv : a ≤ g⁻¹ := by
    simpa [ha, hg] using liEvenCrossOrderedEndpointAmplitude_le_inv L
  have hxLower : g / 64 ≤ (64 * a)⁻¹ := by
    have hscale : 64 * a ≤ 64 * g⁻¹ := by gcongr
    have hinv : (64 * g⁻¹)⁻¹ ≤ (64 * a)⁻¹ :=
      (inv_le_inv₀ (by positivity : 0 < 64 * g⁻¹)
        (by positivity : 0 < 64 * a)).2 hscale
    calc
      g / 64 = (64 * g⁻¹)⁻¹ := by
        field_simp [hgPos.ne']
      _ ≤ (64 * a)⁻¹ := hinv
  have hyLower : (16 * g)⁻¹ ≤ g2⁻¹ / 2 := by
    have htwice : 2 * g2 ≤ 16 * g := by
      nlinarith
    have hinv : (16 * g)⁻¹ ≤ (2 * g2)⁻¹ :=
      (inv_le_inv₀ (by positivity : 0 < 16 * g)
        (by positivity : 0 < 2 * g2)).2 htwice
    calc
      (16 * g)⁻¹ ≤ (2 * g2)⁻¹ := hinv
      _ = g2⁻¹ / 2 := by field_simp [hg2Pos.ne']
  have hLReal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hsucc : (L : ℝ) + 1 ≤ 2 * L := by linarith
  have hgLinear : g ≤ 2 * C * L := by
    calc
      g ≤ C * ((L : ℝ) + 1) := by simpa [hg] using hlinear
      _ ≤ C * (2 * L) := mul_le_mul_of_nonneg_left hsucc hC.le
      _ = 2 * C * L := by ring
  have hLOverG : 1 / (2 * C) ≤ (L : ℝ) / g := by
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * C) hgPos]
    simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using hgLinear
  calc
    1 / (8192 * Real.pi * C) =
        (1 / (2 * C)) / (4096 * Real.pi) := by
      field_simp [hC.ne', Real.pi_ne_zero]
      norm_num
    _ ≤ ((L : ℝ) / g) / (4096 * Real.pi) := by gcongr
    _ = (L : ℝ) * (4 / Real.pi) * (g / 64) * ((16 * g)⁻¹) ^ (2 : ℕ) := by
      field_simp [hgPos.ne', Real.pi_ne_zero]
      ring
    _ ≤ (L : ℝ) * (4 / Real.pi) * (64 * a)⁻¹ * (g2⁻¹ / 2) ^ (2 : ℕ) := by
      gcongr
    _ = (L : ℝ) * ((4 / Real.pi) *
        (64 * liEvenCrossOrderedEndpointAmplitude L)⁻¹ *
        ((xiOrderedPositiveOrdinate (2 * L))⁻¹ / 2) ^ (2 : ℕ)) := by
      simp only [a, g2]
      ring

/-- Cofinal dyadic critical shells carry a uniform positive normalized-current floor. -/
theorem exists_pos_eventually_liEvenCrossFullCriticalNormalizedTail_dyadic_lower
    (q : ℕ → XiCriticalLineResolventCopy)
    (hordinate : ∀ n : ℕ,
      ((q n).1.1 : ℂ).im = xiOrderedPositiveOrdinate n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ L : ℕ in atTop,
      δ ≤ liEvenCrossFullCriticalNormalizedTail q L (2 * L)
        (liEvenCrossOrderedEndpointResonantMode L) := by
  obtain ⟨C, hC, hlinear⟩ :=
    exists_eventually_xiOrderedPositiveOrdinate_le_linear
  refine ⟨1 / (8192 * Real.pi * C), by positivity, ?_⟩
  have hgamma : ∀ᶠ L : ℕ in atTop,
      64 ≤ xiOrderedPositiveOrdinate L :=
    tendsto_xiOrderedPositiveOrdinate_atTop (eventually_ge_atTop 64)
  filter_upwards [hlinear,
    eventually_xiOrderedPositiveOrdinate_two_mul_le_eight_mul,
    hgamma, eventually_ge_atTop 1] with L hlinearL hdyadicL hgammaL hL
  exact (liEvenCrossFullCriticalNormalizedTail_dyadic_scalar_lower
    hL hC hlinearL hdyadicL).trans
      (liEvenCrossFullCriticalNormalizedTail_dyadic_lower
        q hordinate hgammaL)

/--
There is no multiplicity-exact critical enumeration whose normalized Li endpoint-current tails
are uniformly Cauchy in the integer mode.
-/
theorem not_exists_liEvenCrossFullCriticalNormalizedUniformCauchy :
    ¬ ∃ q : ℕ → XiCriticalLineResolventCopy,
      (∀ n : ℕ, ((q n).1.1 : ℂ).im = xiOrderedPositiveOrdinate n) ∧
      LiEvenCrossFullCriticalNormalizedUniformCauchy q := by
  rintro ⟨q, hordinate, hCauchy⟩
  obtain ⟨δ, hδ, hfloor⟩ :=
    exists_pos_eventually_liEvenCrossFullCriticalNormalizedTail_dyadic_lower
      q hordinate
  obtain ⟨N, hN⟩ := hCauchy δ hδ
  rw [eventually_atTop] at hfloor
  obtain ⟨K, hK⟩ := hfloor
  let L := max N (max K 1)
  have hNL : N ≤ L := by simp [L]
  have hKL : K ≤ L := by simp [L]
  have htailLower := hK L hKL
  have htailSmall := hN L (2 * L)
    (liEvenCrossOrderedEndpointResonantMode L) hNL (by omega)
  have htailAbs :
      liEvenCrossFullCriticalNormalizedTail q L (2 * L)
          (liEvenCrossOrderedEndpointResonantMode L) ≤
        |liEvenCrossFullCriticalNormalizedTail q L (2 * L)
          (liEvenCrossOrderedEndpointResonantMode L)| :=
    le_abs_self _
  linarith

end

end RHTower
