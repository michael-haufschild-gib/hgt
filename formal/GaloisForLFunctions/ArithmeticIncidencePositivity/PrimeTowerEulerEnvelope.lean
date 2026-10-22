import GaloisForLFunctions.ArithmeticIncidencePositivity.TranslatePairingCalculus

/-!
# The Euler-factor envelope of a prime tower and its first-power discount

The prime side of the zero form of a test `F` is `Σ_{n ≥ 2} 2Λ(n) n^{−1/2} A(log n)` with
`A = autoCorr F`; the incidence ledger reads it strip by strip, one strip per prime power. This
file reads it **tower by tower**: for a fixed prime `p` the atoms of `p, p², p³, …` sit at the
arithmetic progression of shifts `k log p` with geometric weights `log p · p^{−k/2}`, so the whole
tower is one geometric lag charge

    C_p(F) = Σ_{k ≥ 1} Λ(p^k) p^{−k/2} A(k log p) = log p · Σ_{k ≥ 1} z^k A(k log p),  z = p^{−1/2}.

For any spacing `L > 0` and any `z ∈ (0,1)` the geometric train `S = Σ_{k ≤ N} z^k F(· + kL)`
satisfies `F = S − z S(· + L)` up to one tail translate, and the two-step square
`∫ (S(u) − S(u + 2L))² du ≥ 0` collapses the resulting relations to

    (1 − z²) Σ_{k ≥ 1} z^k A(kL) ≤ z² A(0) + z A(L),

that is `Σ_{k ≥ 1} z^k A(kL) ≤ z/(1−z) · A(0) − z/(1−z²) · (A(0) − A(L))`: the Euler-factor
envelope `z/(1−z) A(0)` discounted by the **first-power fold defect** `A(0) − A(L)`. At `z = p^{−1/2}`,
`L = log p` this is

    (p − 1) · C_p(F) ≤ log p · (A(0) + √p · A(log p)),

so the charge of a whole prime tower is controlled by the single datum `A(log p)`: the proper prime
powers carry no information of their own beyond the Euler constants, and a test uncorrelated at the
prime shift charges the tower at most `log p/(p−1)` instead of the envelope `log p/(√p−1)`.
-/

open MeasureTheory Set
open scoped ArithmeticFunction
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {F A B₁ B₂ : ℝ → ℝ}

/-! ### The lag charge and the envelope law -/

/-- The geometric lag charge `Σ_{m ≥ 1} z^m A(mL)` at spacing `L`: at `z = p^{−1/2}`,
`L = log p` it is the charge of the whole tower of `p` divided by `log p`. -/
def geoLagCharge (z L : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∑' m : ℕ, z ^ (m + 1) * autoCorr F (((m : ℝ) + 1) * L)

/-- For a compactly supported test the lag charge is a finite sum: lags beyond the support
diameter carry no autocorrelation. -/
theorem geoLagCharge_eq_sum {B z L : ℝ} (hsupp : ∀ x, B < |x| → F x = 0) (hL : 0 < L)
    {N : ℕ} (hN : 2 * B < ((N : ℝ) + 1) * L) :
    geoLagCharge z L F
      = ∑ m ∈ Finset.range (N + 1), z ^ (m + 1) * autoCorr F (((m : ℝ) + 1) * L) := by
  refine tsum_eq_sum fun m hm => ?_
  have hmN : N + 1 ≤ m := by
    rcases Nat.lt_or_ge m (N + 1) with h | h
    · exact absurd (Finset.mem_range.mpr h) hm
    · exact h
  have hcast : (N : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hmN
  have hmono : ((N : ℝ) + 1) * L ≤ ((m : ℝ) + 1) * L :=
    mul_le_mul_of_nonneg_right (by linarith) hL.le
  have hpos : 0 < ((m : ℝ) + 1) * L := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    positivity
  rw [autoCorr_eq_zero_of_support hsupp (by rw [abs_of_pos hpos]; linarith), mul_zero]

/-- **The Euler-factor envelope with its first-lag discount.** For every continuous test supported
in `[−B, B]`, every spacing `L > 0` and every `z ∈ (0,1)`,

    (1 − z²) · Σ_{m ≥ 1} z^m A(mL) ≤ z² A(0) + z A(L),

equivalently `Σ_{m ≥ 1} z^m A(mL) ≤ z/(1−z) · A(0) − z/(1−z²) · (A(0) − A(L))`: the geometric lag
charge never exceeds its Euler envelope `z/(1−z) A(0)`, and the gap is at least `z/(1−z²)` times
the first-lag fold defect. The proof is the resolvent identity of the geometric train
`S_N = Σ_{k ≤ N} z^k F(· + kL)` together with the two-step square `A_S(0) ≥ A_S(2L)`. -/
theorem one_sub_sq_mul_geoLagCharge_le {B z L : ℝ} (hF : Continuous F) (hB : 0 ≤ B)
    (hsupp : ∀ x, B < |x| → F x = 0) (hzabs : |z| < 1) (hL : 0 < L) :
    (1 - z ^ 2) * geoLagCharge z L F ≤ z ^ 2 * autoCorr F 0 + z * autoCorr F L := by
  have hFc : HasCompactSupport F := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -B) (b := B)) fun x hx => hsupp x ?_
    rcases lt_or_ge x (-B) with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · have hxB : B < x := by
        by_contra hc
        exact hx (Set.mem_Icc.mpr ⟨h, not_lt.mp hc⟩)
      rw [abs_of_pos (by linarith)]
      exact hxB
  have hFn : ContCompact F := ⟨hF, hFc⟩
  have h0 : 0 ≤ autoCorr F 0 := autoCorr_zero_nonneg hF hFc
  have hz1 : z < 1 := (abs_lt.mp hzabs).2
  have hzA0 : (0 : ℝ) ≤ |z| := abs_nonneg z
  have hza : |z| ≤ 1 := hzabs.le
  have hz : (0 : ℝ) < 1 - z := by linarith
  have hzA : (0 : ℝ) < 1 - |z| := by linarith
  have hM1 : (1 : ℝ) ≤ 1 / (1 - |z|) := by rw [le_div_iff₀ hzA]; linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- choose a truncation whose tail is below `ε`
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, 2 * B < ((N : ℝ) + 1) * L ∧
      11 * (1 / (1 - |z|)) * (autoCorr F 0 + 1) * |z| ^ (N + 1) < ε := by
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 * B / L)
    have hpow : Filter.Tendsto
        (fun n : ℕ => 11 * (1 / (1 - |z|)) * (autoCorr F 0 + 1) * |z| ^ (n + 1))
        Filter.atTop (nhds 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hzA0 hzabs).comp
        (Filter.tendsto_add_atTop_nat 1)
      simpa using h.const_mul (11 * (1 / (1 - |z|)) * (autoCorr F 0 + 1))
    obtain ⟨N, hNge, hNlt⟩ := ((Filter.eventually_ge_atTop N₁).and
      (hpow.eventually (gt_mem_nhds hε))).exists
    refine ⟨N, ?_, hNlt⟩
    have hlt : 2 * B / L < (N : ℝ) := lt_of_lt_of_le hN₁ (by exact_mod_cast hNge)
    rw [div_lt_iff₀ hL] at hlt
    nlinarith
  -- the train and its tail
  obtain ⟨S, hS⟩ : ∃ S : ℝ → ℝ, S = geoTrain z L F N := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, G = geoTail z L F N := ⟨_, rfl⟩
  have nS : ContCompact S := by rw [hS, geoTrain]; exact hFn.comb _ _ _
  have nG : ContCompact G := by rw [hG, geoTail]; exact hFn.comb _ _ _
  have nT1 : ContCompact (fun u => S (u + L)) := nS.translate L
  have nT2 : ContCompact (fun u => S (u + 2 * L)) := nS.translate (2 * L)
  have nG1 : ContCompact (fun u => G (u + L)) := nG.translate L
  -- pairings internal to the train
  have pSS : testPairing S S = autoCorr S 0 := by
    rw [autoCorr_eq_testPairing]
    exact congrArg (testPairing S) (by funext u; rw [add_zero])
  have pST1 : testPairing S (fun u => S (u + L)) = autoCorr S L := rfl
  have pST2 : testPairing S (fun u => S (u + 2 * L)) = autoCorr S (2 * L) := rfl
  have pT1T1 : testPairing (fun u => S (u + L)) (fun u => S (u + L)) = autoCorr S 0 := by
    rw [testPairing_translate S S L, pSS]
  have pT1T2 : testPairing (fun u => S (u + L)) (fun u => S (u + 2 * L)) = autoCorr S L := by
    have h : (fun u => S (u + 2 * L)) = fun u => (fun v => S (v + L)) (u + L) := by
      funext u
      show S (u + 2 * L) = S (u + L + L)
      rw [show u + L + L = u + 2 * L by ring]
    rw [h, testPairing_translate S (fun v => S (v + L)) L, ← autoCorr_eq_testPairing]
  -- the resolvent split of the test
  have hsplit : ∀ u, F u = (S u - z * S (u + L)) + G u := by
    intro u
    rw [hS, hG]
    linarith [geoTrain_resolvent z L F N u]
  have hFfun : F = fun u => (S u - z * S (u + L)) + G u := funext hsplit
  have hFfunL : (fun u => F (u + L))
      = fun u => (S (u + L) - z * S (u + 2 * L)) + G (u + L) := by
    funext u
    rw [hsplit (u + L), show u + L + L = u + 2 * L by ring]
  -- the three relations
  have relA : autoCorr F 0 = (1 + z ^ 2) * autoCorr S 0 - 2 * z * autoCorr S L
      + (2 * testPairing S G - 2 * z * testPairing (fun u => S (u + L)) G + testPairing G G) := by
    have h1 : autoCorr F 0 = testPairing F F := by
      rw [autoCorr_eq_testPairing]
      exact congrArg (testPairing F) (by funext u; rw [add_zero])
    rw [h1, hFfun, testPairing_add_add (nS.sub_nice (ContCompact.const_mul_nice z nT1)) nG
      (nS.sub_nice (ContCompact.const_mul_nice z nT1)) nG,
      testPairing_sub_smul_sub_smul nS nT1 nS nT1 z, testPairing_sub_smul_left nS nT1 nG z,
      testPairing_comm G (fun u => S u - z * S (u + L)), testPairing_sub_smul_left nS nT1 nG z,
      pSS, pST1, pT1T1, testPairing_comm (fun u => S (u + L)) S, pST1]
    ring
  have relB : autoCorr F L = (1 + z ^ 2) * autoCorr S L
      - z * (autoCorr S 0 + autoCorr S (2 * L))
      + (testPairing S (fun u => G (u + L)) - z * testPairing (fun u => S (u + L)) (fun u => G (u + L))
        + testPairing (fun u => S (u + L)) G - z * testPairing (fun u => S (u + 2 * L)) G
        + testPairing G (fun u => G (u + L))) := by
    have h1 : autoCorr F L = testPairing F (fun u => F (u + L)) := rfl
    rw [h1, hFfunL, hFfun, testPairing_add_add (nS.sub_nice (ContCompact.const_mul_nice z nT1)) nG
      (nT1.sub_nice (ContCompact.const_mul_nice z nT2)) nG1,
      testPairing_sub_smul_sub_smul nS nT1 nT1 nT2 z, testPairing_sub_smul_left nS nT1 nG1 z,
      testPairing_comm G (fun u => S (u + L) - z * S (u + 2 * L)),
      testPairing_sub_smul_left nT1 nT2 nG z, pST1, pST2, pT1T1, pT1T2]
    ring
  have relC : geoLagCharge z L F
      = z * autoCorr S L - z ^ 2 * autoCorr S 0 + z * testPairing (fun u => S (u + L)) G := by
    have hcharge : geoLagCharge z L F
        = z * ∑ k ∈ Finset.range (N + 1), z ^ k * autoCorr F ((k : ℝ) * L + L) := by
      rw [geoLagCharge_eq_sum hsupp hL hN1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show ((k : ℝ) + 1) * L = (k : ℝ) * L + L by ring]
      ring
    have hpair : testPairing F (fun u => S (u + L))
        = ∑ k ∈ Finset.range (N + 1), z ^ k * autoCorr F ((k : ℝ) * L + L) := by
      rw [hS, geoTrain_shift z L F N L]
      exact testPairing_test_comb hFn _ _ _
    have hexp : testPairing F (fun u => S (u + L))
        = autoCorr S L - z * autoCorr S 0 + testPairing (fun u => S (u + L)) G := by
      rw [hFfun, testPairing_add_left (nS.sub_nice (ContCompact.const_mul_nice z nT1)) nG nT1,
        testPairing_sub_smul_left nS nT1 nT1 z, pST1, pT1T1, testPairing_comm G (fun u => S (u + L))]
    rw [hcharge, ← hpair, hexp]
    ring
  -- the tail bounds
  have hzpow : (0 : ℝ) ≤ |z| ^ (N + 1) := pow_nonneg hzA0 (N + 1)
  have hmassS : ∑ k ∈ Finset.range (N + 1), |z ^ k| ≤ 1 / (1 - |z|) :=
    sum_abs_pow_le_inv_one_sub_abs hzabs (N + 1)
  have hmassG : ∑ _j ∈ Finset.range 1, |z ^ (N + 1)| ≤ |z| ^ (N + 1) := by
    simp [abs_pow]
  have hmassG' : ∑ _j ∈ Finset.range 1, |z ^ (N + 1)| ≤ 1 / (1 - |z|) :=
    le_trans hmassG (le_trans (pow_le_one₀ hzA0 hza) hM1)
  have bound : ∀ s t : ℝ,
      |testPairing (translateComb F (N + 1) (fun k => z ^ k) (fun k => (k : ℝ) * L + s))
            (translateComb F 1 (fun _ => z ^ (N + 1)) (fun _ => ((N : ℝ) + 1) * L + t))|
        ≤ 1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0) := fun s t =>
    abs_testPairing_comb_le hFn hmassS hmassG hzpow
  have boundGG : ∀ t : ℝ,
      |testPairing G (translateComb F 1 (fun _ => z ^ (N + 1)) (fun _ => ((N : ℝ) + 1) * L + t))|
        ≤ 1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0) := by
    intro t
    rw [hG, geoTail]
    exact abs_testPairing_comb_le hFn hmassG' hmassG hzpow
  -- all seven tail pairings are below one common bound
  have key : 0 ≤ 1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0) :=
    mul_nonneg (div_nonneg zero_le_one hzA.le) (mul_nonneg hzpow h0)
  have bSG : |testPairing S G| ≤ 1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0) := by
    have h := bound 0 0
    simp only [add_zero] at h
    rw [hS, hG, geoTrain, geoTail]
    exact h
  have bT1G : |testPairing (fun u => S (u + L)) G| ≤ 1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0) := by
    have h := bound L 0
    simp only [add_zero] at h
    rw [hS, geoTrain_shift z L F N L, hG, geoTail]
    exact h
  have bT2G : |testPairing (fun u => S (u + 2 * L)) G|
      ≤ 1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0) := by
    have h := bound (2 * L) 0
    simp only [add_zero] at h
    rw [hS, geoTrain_shift z L F N (2 * L), hG, geoTail]
    exact h
  have bSG1 : |testPairing S (fun u => G (u + L))|
      ≤ 1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0) := by
    have h := bound 0 L
    simp only [add_zero] at h
    rw [hS, geoTrain, hG, geoTail_shift z L F N L]
    exact h
  have bT1G1 : |testPairing (fun u => S (u + L)) (fun u => G (u + L))|
      ≤ 1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0) := by
    have h := bound L L
    rw [hS, geoTrain_shift z L F N L, hG, geoTail_shift z L F N L]
    exact h
  have bGG : |testPairing G G| ≤ 1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0) := by
    have h := boundGG 0
    simp only [add_zero] at h
    rw [hG] at h ⊢
    rw [geoTail]
    exact h
  have bGG1 : |testPairing G (fun u => G (u + L))|
      ≤ 1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0) := by
    have h := boundGG L
    rw [hG] at h ⊢
    rw [geoTail_shift z L F N L]
    exact h
  -- the identity and the conclusion
  have hXY2 : autoCorr S (2 * L) ≤ autoCorr S 0 :=
    le_trans (le_abs_self _) (abs_autoCorr_le_autoCorr_zero nS.1 nS.2 (2 * L))
  have hsq : 0 ≤ z ^ 2 * (autoCorr S 0 - autoCorr S (2 * L)) :=
    mul_nonneg (sq_nonneg z) (by linarith only [hXY2])
  -- each tail term is its coefficient times a pairing below the common tail bound
  have step : ∀ c q C : ℝ, |q| ≤ 1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0) → |c| ≤ C →
      0 ≤ C → -(C * (1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0))) ≤ c * q := by
    intro c q C hq hc hC
    have h1 : |c * q| ≤ C * (1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0)) := by
      rw [abs_mul]
      exact mul_le_mul hc hq (abs_nonneg q) hC
    linarith only [(abs_le.mp h1).1]
  have habsz2 : |z ^ 2| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ hzA0 hza
  have habs2 : |2 * z ^ 2| ≤ 2 := by
    rw [abs_mul, abs_two]; linarith only [habsz2]
  have habs3 : |-(z ^ 3)| ≤ 1 := by
    rw [abs_neg, abs_pow]; exact pow_le_one₀ hzA0 hza
  have habsnz2 : |-(z ^ 2)| ≤ 1 := by rw [abs_neg]; exact habsz2
  have habsz : |z| ≤ 1 := hza
  have t1 := step _ _ 2 bSG habs2 (by norm_num)
  have t2 := step _ _ 1 bT1G habs3 zero_le_one
  have t3 := step _ _ 1 bGG habsz2 zero_le_one
  have t4 := step _ _ 1 bSG1 habsz zero_le_one
  have t5 := step _ _ 1 bT1G1 habsnz2 zero_le_one
  have t6 := step _ _ 1 bT2G habsnz2 zero_le_one
  have t7 := step _ _ 1 bGG1 habsz zero_le_one
  -- collapse the tail into one scalar
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0) := ⟨_, rfl⟩
  rw [← hP] at t1 t2 t3 t4 t5 t6 t7
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 2 * z ^ 2 * testPairing S G
      + (-(z ^ 3)) * testPairing (fun u => S (u + L)) G
      + z ^ 2 * testPairing G G
      + z * testPairing S (fun u => G (u + L))
      + (-(z ^ 2)) * testPairing (fun u => S (u + L)) (fun u => G (u + L))
      + (-(z ^ 2)) * testPairing (fun u => S (u + 2 * L)) G
      + z * testPairing G (fun u => G (u + L)) := ⟨_, rfl⟩
  have hEb : -(8 * P) ≤ E := by
    rw [hE]; linarith only [t1, t2, t3, t4, t5, t6, t7]
  have hid : z ^ 2 * autoCorr F 0 + z * autoCorr F L - (1 - z ^ 2) * geoLagCharge z L F
      = z ^ 2 * (autoCorr S 0 - autoCorr S (2 * L)) + E := by
    rw [hE, relA, relB, relC]; ring
  have h8 : 8 * P ≤ 11 * (1 / (1 - |z|)) * (autoCorr F 0 + 1) * |z| ^ (N + 1) := by
    have hc0 : 0 ≤ 1 / (1 - |z|) * |z| ^ (N + 1) :=
      mul_nonneg (div_nonneg zero_le_one hzA.le) hzpow
    have hrw : 11 * (1 / (1 - |z|)) * (autoCorr F 0 + 1) * |z| ^ (N + 1)
        - 8 * (1 / (1 - |z|) * (|z| ^ (N + 1) * autoCorr F 0))
        = 1 / (1 - |z|) * |z| ^ (N + 1) * (3 * autoCorr F 0 + 11) := by ring
    have hprod : 0 ≤ 1 / (1 - |z|) * |z| ^ (N + 1) * (3 * autoCorr F 0 + 11) :=
      mul_nonneg hc0 (by linarith only [h0])
    rw [hP]
    linarith only [hrw, hprod]
  linarith only [hid, hsq, hEb, h8, hN2]

/-- The envelope-minus-discount form: `Σ_{m≥1} z^m A(mL) ≤ z/(1−z) A(0) − z/(1−z²) (A(0) − A(L))`. -/
theorem geoLagCharge_le_envelope_sub_discount {B z L : ℝ} (hF : Continuous F) (hB : 0 ≤ B)
    (hsupp : ∀ x, B < |x| → F x = 0) (hz0 : 0 < z) (hz1 : z < 1) (hL : 0 < L) :
    geoLagCharge z L F ≤ z / (1 - z) * autoCorr F 0
      - z / (1 - z ^ 2) * (autoCorr F 0 - autoCorr F L) := by
  have key := one_sub_sq_mul_geoLagCharge_le hF hB hsupp
    (by rw [abs_of_pos hz0]; exact hz1) hL
  have hpos : (0 : ℝ) < 1 - z ^ 2 := by nlinarith
  have hid : z / (1 - z) * autoCorr F 0 - z / (1 - z ^ 2) * (autoCorr F 0 - autoCorr F L)
      = (z ^ 2 * autoCorr F 0 + z * autoCorr F L) / (1 - z ^ 2) := by
    have h1 : (1 : ℝ) - z ≠ 0 := by linarith
    have h2 : (1 : ℝ) - z ^ 2 ≠ 0 := ne_of_gt hpos
    field_simp
    ring
  rw [hid, le_div_iff₀ hpos]
  linarith only [key]

/-! ### The tower of one prime -/

/-- The tower charge `C_p(F) = Σ_{k ≥ 1} Λ(p^k) p^{−k/2} A(k log p)`: the part of the prime side of
the zero form carried by the powers of one prime. -/
def towerCharge (p : ℕ) (F : ℝ → ℝ) : ℝ :=
  ∑' k : ℕ, RHTower.vonMangoldtAtom (p ^ (k + 1)) * autoCorr F (((k : ℝ) + 1) * Real.log p)

/-- The atoms of a tower are geometric with ratio `p^{−1/2}`. -/
theorem vonMangoldtAtom_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    RHTower.vonMangoldtAtom (p ^ (k + 1)) = Real.log p * (1 / Real.sqrt p) ^ (k + 1) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hple : 2 ≤ p ^ (k + 1) := le_trans hp.two_le (Nat.le_self_pow (Nat.succ_ne_zero k) p)
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hps : (Real.sqrt p ^ (k + 1)) ^ 2 = (p : ℝ) ^ (k + 1) := by
    rw [← pow_mul, mul_comm (k + 1) 2, pow_mul, Real.sq_sqrt hp0]
  have hsqrt : Real.sqrt ((p : ℝ) ^ (k + 1)) = Real.sqrt p ^ (k + 1) := by
    rw [← hps, Real.sqrt_sq (by positivity)]
  have hatom : RHTower.vonMangoldtAtom (p ^ (k + 1))
      = ArithmeticFunction.vonMangoldt (p ^ (k + 1)) / Real.sqrt ((p ^ (k + 1) : ℕ) : ℝ) := by
    simp only [RHTower.vonMangoldtAtom, if_pos hple]
  rw [hatom, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, hsqrt, one_div, inv_pow,
    div_eq_mul_inv]

/-- The tower charge is `log p` times the geometric lag charge at `z = p^{−1/2}`, `L = log p`. -/
theorem towerCharge_eq_log_mul_geoLagCharge {p : ℕ} (hp : p.Prime) (F : ℝ → ℝ) :
    towerCharge p F = Real.log p * geoLagCharge (1 / Real.sqrt p) (Real.log p) F := by
  rw [towerCharge, geoLagCharge, ← tsum_mul_left]
  exact tsum_congr fun k => by rw [vonMangoldtAtom_prime_pow hp]; ring

/-- **The prime tower law.** For every continuous test supported in `[−B, B]` and every prime `p`,

    (p − 1) · C_p(F) ≤ log p · (A(0) + √p · A(log p)),

so the charge of the whole tower of `p` is controlled by the single first-power datum `A(log p)`.
At full resonance `A(log p) = A(0)` the right side is the Euler envelope `log p/(√p − 1) · A(0)`;
a test uncorrelated at the prime shift charges the whole tower at most `log p/(p − 1) · A(0)`. -/
theorem sub_one_mul_towerCharge_le {p : ℕ} {B : ℝ} (hp : p.Prime) (hF : Continuous F) (hB : 0 ≤ B)
    (hsupp : ∀ x, B < |x| → F x = 0) :
    ((p : ℝ) - 1) * towerCharge p F
      ≤ Real.log p * (autoCorr F 0 + Real.sqrt p * autoCorr F (Real.log p)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hsp1 : 1 < Real.sqrt p := by
    have h := Real.sqrt_lt_sqrt zero_le_one hp1
    simpa using h
  have hsp0 : 0 < Real.sqrt p := by linarith
  have hsq : Real.sqrt p ^ 2 = (p : ℝ) := Real.sq_sqrt hp0.le
  have hz0 : 0 < 1 / Real.sqrt p := by positivity
  have hz1 : 1 / Real.sqrt p < 1 := by rw [div_lt_one hsp0]; exact hsp1
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have key := one_sub_sq_mul_geoLagCharge_le hF hB hsupp
    (by rw [abs_of_pos hz0]; exact hz1) hlog
  have hz2 : (1 / Real.sqrt p) ^ 2 = 1 / (p : ℝ) := by rw [div_pow, one_pow, hsq]
  rw [hz2] at key
  have hps : (p : ℝ) / Real.sqrt p = Real.sqrt p := by
    field_simp
    linear_combination -hsq
  have hT : ((p : ℝ) - 1) * geoLagCharge (1 / Real.sqrt p) (Real.log p) F
      ≤ autoCorr F 0 + Real.sqrt p * autoCorr F (Real.log p) := by
    have h := mul_le_mul_of_nonneg_left key hp0.le
    have e1 : (p : ℝ) * ((1 - 1 / (p : ℝ)) * geoLagCharge (1 / Real.sqrt p) (Real.log p) F)
        = ((p : ℝ) - 1) * geoLagCharge (1 / Real.sqrt p) (Real.log p) F := by
      field_simp
    have e2 : (p : ℝ) * (1 / (p : ℝ) * autoCorr F 0
          + 1 / Real.sqrt p * autoCorr F (Real.log p))
        = autoCorr F 0 + Real.sqrt p * autoCorr F (Real.log p) := by
      rw [mul_add, ← mul_assoc, ← mul_assoc, mul_one_div, div_self hp0.ne', one_mul,
        mul_one_div, hps]
    rw [e1, e2] at h
    exact h
  calc ((p : ℝ) - 1) * towerCharge p F
      = Real.log p * (((p : ℝ) - 1) * geoLagCharge (1 / Real.sqrt p) (Real.log p) F) := by
        rw [towerCharge_eq_log_mul_geoLagCharge hp]; ring
    _ ≤ Real.log p * (autoCorr F 0 + Real.sqrt p * autoCorr F (Real.log p)) :=
        mul_le_mul_of_nonneg_left hT hlog.le

/-! ### The prime side is a sum of tower charges -/

/-- Only prime powers carry an atom. -/
theorem vonMangoldtAtom_eq_zero_of_not_isPrimePow {n : ℕ} (hn : ¬ IsPrimePow n) :
    RHTower.vonMangoldtAtom n = 0 := by
  by_cases h2 : 2 ≤ n
  · simp only [RHTower.vonMangoldtAtom, if_pos h2,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div]
  · simp only [RHTower.vonMangoldtAtom, if_neg h2]

/-- The prime side of the zero form: `Σ_{n ≥ 2} Λ(n) n^{−1/2} A(log n)`. -/
def primeSideCharge (F : ℝ → ℝ) : ℝ := ∑' n : ℕ, RHTower.vonMangoldtAtom n * autoCorr F (Real.log n)

/-- Beyond the horizon `e^{2B}` an atom sees no autocorrelation. -/
theorem autoCorr_eq_zero_beyond_horizon {B : ℝ} (hB : 0 ≤ B) (hsupp : ∀ x, B < |x| → F x = 0) {t : ℝ}
    (ht : 2 * B < t) : autoCorr F t = 0 := by
  have hpos : 0 < t := by linarith
  exact autoCorr_eq_zero_of_support hsupp (by rw [abs_of_pos hpos]; exact ht)

/-- The prime side has finite support: only `n ≤ e^{2B}` contributes. -/
theorem primeSideCharge_summable {B : ℝ} (hB : 0 ≤ B) (hsupp : ∀ x, B < |x| → F x = 0) :
    Summable fun n : ℕ => RHTower.vonMangoldtAtom n * autoCorr F (Real.log n) := by
  refine summable_of_ne_finset_zero (s := Finset.range (⌈Real.exp (2 * B)⌉₊ + 1)) fun n hn => ?_
  have hlt : ⌈Real.exp (2 * B)⌉₊ < n := by
    rcases Nat.lt_or_ge (⌈Real.exp (2 * B)⌉₊) n with h | h
    · exact h
    · exact absurd (Finset.mem_range.mpr (by omega)) hn
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hlt
  have hexp : Real.exp (2 * B) < (n : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hlt)
  have hlog : 2 * B < Real.log n := by
    have := Real.log_lt_log (Real.exp_pos (2 * B)) hexp
    rwa [Real.log_exp] at this
  rw [autoCorr_eq_zero_beyond_horizon hB hsupp hlog, mul_zero]

/-- **The prime side is the sum of the tower charges.** -/
theorem primeSideCharge_eq_tsum_towerCharge {B : ℝ} (hB : 0 ≤ B) (hsupp : ∀ x, B < |x| → F x = 0) :
    primeSideCharge F = ∑' p : Nat.Primes, towerCharge (p : ℕ) F := by
  classical
  have hsum := primeSideCharge_summable hB hsupp
  have hsupport :
      (Function.support fun n : ℕ => RHTower.vonMangoldtAtom n * autoCorr F (Real.log n))
        ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hcon
    exact hn (by
      show RHTower.vonMangoldtAtom n * autoCorr F (Real.log n) = 0
      rw [vonMangoldtAtom_eq_zero_of_not_isPrimePow hcon, zero_mul])
  have hrestrict : (∑' n : {n : ℕ // IsPrimePow n},
        RHTower.vonMangoldtAtom (n : ℕ) * autoCorr F (Real.log (n : ℕ)))
      = ∑' n : ℕ, RHTower.vonMangoldtAtom n * autoCorr F (Real.log n) :=
    tsum_subtype_eq_of_support_subset hsupport
  have hterm : ∀ x : Nat.Primes × ℕ,
      RHTower.vonMangoldtAtom ((Nat.Primes.prodNatEquiv x : ℕ))
          * autoCorr F (Real.log ((Nat.Primes.prodNatEquiv x : ℕ)))
        = RHTower.vonMangoldtAtom ((x.1 : ℕ) ^ (x.2 + 1))
          * autoCorr F (((x.2 : ℝ) + 1) * Real.log (x.1 : ℕ)) := by
    rintro ⟨p, a⟩
    have hval : ((Nat.Primes.prodNatEquiv (p, a) : {n : ℕ // IsPrimePow n}) : ℕ)
        = (p : ℕ) ^ (a + 1) := rfl
    rw [hval, Nat.cast_pow, Real.log_pow]
    push_cast
    ring_nf
  have hreindex : (∑' x : Nat.Primes × ℕ, RHTower.vonMangoldtAtom ((x.1 : ℕ) ^ (x.2 + 1))
        * autoCorr F (((x.2 : ℝ) + 1) * Real.log (x.1 : ℕ)))
      = ∑' n : {n : ℕ // IsPrimePow n},
          RHTower.vonMangoldtAtom (n : ℕ) * autoCorr F (Real.log (n : ℕ)) := by
    rw [← Nat.Primes.prodNatEquiv.tsum_eq (fun n : {n : ℕ // IsPrimePow n} =>
      RHTower.vonMangoldtAtom (n : ℕ) * autoCorr F (Real.log (n : ℕ)))]
    exact tsum_congr fun x => (hterm x).symm
  have hsummableProd : Summable fun x : Nat.Primes × ℕ =>
      RHTower.vonMangoldtAtom ((x.1 : ℕ) ^ (x.2 + 1))
        * autoCorr F (((x.2 : ℝ) + 1) * Real.log (x.1 : ℕ)) := by
    have hsub : Summable fun n : {n : ℕ // IsPrimePow n} =>
        RHTower.vonMangoldtAtom (n : ℕ) * autoCorr F (Real.log (n : ℕ)) := hsum.subtype _
    exact ((Nat.Primes.prodNatEquiv.summable_iff
      (f := fun n : {n : ℕ // IsPrimePow n} =>
        RHTower.vonMangoldtAtom (n : ℕ) * autoCorr F (Real.log (n : ℕ)))).mpr hsub).congr
      fun x => hterm x
  rw [primeSideCharge, ← hrestrict, ← hreindex, hsummableProd.tsum_prod]
  exact tsum_congr fun p => rfl

/-- The division form of the tower law. -/
theorem towerCharge_le_div {p : ℕ} {B : ℝ} (hp : p.Prime) (hF : Continuous F) (hB : 0 ≤ B)
    (hsupp : ∀ x, B < |x| → F x = 0) :
    towerCharge p F ≤ Real.log p / ((p : ℝ) - 1)
      * (autoCorr F 0 + Real.sqrt p * autoCorr F (Real.log p)) := by
  have h := sub_one_mul_towerCharge_le hp hF hB hsupp
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith only [h]

/-- A prime beyond the horizon carries no tower charge. -/
theorem towerCharge_eq_zero_of_horizon {p : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hsupp : ∀ x, B < |x| → F x = 0) (hhor : 2 * B < Real.log p) : towerCharge p F = 0 := by
  have hlp : 0 < Real.log p := by linarith
  have hterm : ∀ k : ℕ, RHTower.vonMangoldtAtom (p ^ (k + 1))
      * autoCorr F (((k : ℝ) + 1) * Real.log p) = 0 := by
    intro k
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : Real.log p ≤ ((k : ℝ) + 1) * Real.log p := by nlinarith
    rw [autoCorr_eq_zero_beyond_horizon hB hsupp (by linarith), mul_zero]
  rw [towerCharge, tsum_congr hterm, tsum_zero]

/-- **The prime side is carried by the primes.** For every continuous test supported in `[−B, B]`
and every finite set `S` of primes containing all primes below the horizon `e^{2B}`,

    Σ_{n ≥ 2} Λ(n) n^{−1/2} A(log n) ≤ Σ_{p ∈ S} log p/(p − 1) · (A(0) + √p · A(log p)).

Every proper prime power is absorbed: the right-hand side is the first-power part of the prime
side inflated by `p/(p − 1) ≤ 2`, plus `A(0) · Σ_{p ∈ S} log p/(p − 1)`, which by Mertens is
`O(B) · A(0)`. The exponential demand of the ledger therefore sits on the primes alone. -/
theorem primeSideCharge_le_sum_primes {T : Finset Nat.Primes} {B : ℝ} (hF : Continuous F) (hB : 0 ≤ B)
    (hsupp : ∀ x, B < |x| → F x = 0)
    (hT : ∀ p : Nat.Primes, Real.log (p : ℕ) ≤ 2 * B → p ∈ T) :
    primeSideCharge F ≤ ∑ p ∈ T, Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)
      * (autoCorr F 0 + Real.sqrt (p : ℕ) * autoCorr F (Real.log (p : ℕ))) := by
  rw [primeSideCharge_eq_tsum_towerCharge hB hsupp]
  have hzero : ∀ p : Nat.Primes, p ∉ T → towerCharge (p : ℕ) F = 0 := by
    intro p hp
    have hhor : 2 * B < Real.log (p : ℕ) := by
      by_contra hcon
      exact hp (hT p (not_lt.mp hcon))
    exact towerCharge_eq_zero_of_horizon hB hsupp hhor
  rw [tsum_eq_sum hzero]
  exact Finset.sum_le_sum fun p _ => towerCharge_le_div p.2 hF hB hsupp

/-! ### The ratio-correlation law of a shift family -/

/-- **The shift-Gram law.** For every continuous compactly supported test, every finite family of
shifts `c` with weights `α`,

    (Σ_k α_k A(c_k))² ≤ A(0) · Σ_{j,k} α_j α_k A(c_k − c_j).

The second factor is the correlation form of the shift family: its diagonal is `A(0) Σ_k α_k²`, and
everything beyond that is carried by the correlations at the *differences* of the shifts. -/
theorem sq_sum_autoCorr_le (hF : Continuous F) (hFc : HasCompactSupport F) (n : ℕ) (α c : ℕ → ℝ) :
    (∑ k ∈ Finset.range n, α k * autoCorr F (c k)) ^ 2
      ≤ autoCorr F 0 * ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          α j * α k * autoCorr F (c k - c j) := by
  have hFn : ContCompact F := ⟨hF, hFc⟩
  have h0 : testPairing F F = autoCorr F 0 := by
    rw [autoCorr_eq_testPairing]
    exact congrArg (testPairing F) (by funext u; rw [add_zero])
  have hcs := testPairing_cauchy_schwarz hFn (hFn.comb n α c)
  rw [testPairing_test_comb hFn n α c, testPairing_comb hFn n n α c α c, h0] at hcs
  exact hcs

/-- Differences of logarithms are logarithms of ratios: the correlation form of the prime shifts is
indexed by the ratios `k/j`, the ratio pairs of the incidence structure. -/
theorem autoCorr_log_sub_log (F : ℝ → ℝ) {j k : ℕ} (hj : j ≠ 0) (hk : k ≠ 0) :
    autoCorr F (Real.log k - Real.log j) = autoCorr F (Real.log ((k : ℝ) / (j : ℝ))) := by
  rw [Real.log_div (Nat.cast_ne_zero.mpr hk) (Nat.cast_ne_zero.mpr hj)]

/-- **The prime-ratio law.** The first-power prime charges of the prime side are controlled by the
correlation form of the prime shifts, whose entries are the autocorrelations at the ratios `k/j`.
Its diagonal is `A(0) Σ_n Λ(n)²/n`, of size `A(0) (log N)²`; the whole gap between the trivial
bound on the prime side and the size of its diagonal is carried by the off-diagonal ratio
correlations. -/
theorem sq_sum_prime_autoCorr_le (hF : Continuous F) (hFc : HasCompactSupport F) (n : ℕ) :
    (∑ k ∈ Finset.range n, RHTower.vonMangoldtAtom k * autoCorr F (Real.log k)) ^ 2
      ≤ autoCorr F 0 * ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k
            * autoCorr F (Real.log k - Real.log j) :=
  sq_sum_autoCorr_le hF hFc n (fun k => RHTower.vonMangoldtAtom k) (fun k => Real.log k)

/-- The off-diagonal part of the prime-shift correlation form: the ratio pairs `(j, k)`, `j ≠ k`,
weighted by their atoms and read at the logarithm of the ratio `k/j`. -/
def ratioOffDiagonal (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
    if j = k then 0
    else RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k
      * autoCorr F (Real.log k - Real.log j)

/-- The correlation form of the prime shifts splits into its diagonal `A(0) Σ Λ(n)²/n` and the
ratio off-diagonal. -/
theorem primeCorrelationForm_eq (F : ℝ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k
          * autoCorr F (Real.log k - Real.log j))
      = (∑ k ∈ Finset.range n, RHTower.vonMangoldtAtom k ^ 2) * autoCorr F 0
        + ratioOffDiagonal F n := by
  classical
  rw [ratioOffDiagonal, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hsplit : ∀ k ∈ Finset.range n,
      RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k
          * autoCorr F (Real.log k - Real.log j)
        = (if j = k then RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k
              * autoCorr F (Real.log k - Real.log j) else 0)
          + (if j = k then 0 else RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k
              * autoCorr F (Real.log k - Real.log j)) := by
    intro k _
    by_cases h : j = k <;> simp [h]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq _ _ _, if_pos hj,
    sub_self]
  ring

/-- **The ratio off-diagonal is the whole difficulty.** If the ratio pairs of a test contribute
nonpositively, the first-power prime side obeys the diagonal bound

    |Σ_{k < n} Λ(k) k^{−1/2} A(log k)| ≤ A(0) · √(Σ_{k < n} Λ(k)²/k),

whose right side is of size `A(0) log n` — the size of the archimedean side — whereas the trivial
bound on the prime side is of size `A(0) √n`. So the replacement hypothesis "the ratio pairs are
not positively correlated" is sufficient for an archimedean-size prime side. -/
theorem abs_sum_prime_autoCorr_le_of_ratioOffDiagonal_nonpos (hF : Continuous F)
    (hFc : HasCompactSupport F) (n : ℕ) (hoff : ratioOffDiagonal F n ≤ 0) :
    |∑ k ∈ Finset.range n, RHTower.vonMangoldtAtom k * autoCorr F (Real.log k)|
      ≤ autoCorr F 0 * Real.sqrt (∑ k ∈ Finset.range n, RHTower.vonMangoldtAtom k ^ 2) := by
  have h0 : 0 ≤ autoCorr F 0 := autoCorr_zero_nonneg hF hFc
  have hdiag : 0 ≤ ∑ k ∈ Finset.range n, RHTower.vonMangoldtAtom k ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have key := sq_sum_prime_autoCorr_le hF hFc n
  rw [primeCorrelationForm_eq] at key
  have hsq : (∑ k ∈ Finset.range n, RHTower.vonMangoldtAtom k * autoCorr F (Real.log k)) ^ 2
      ≤ (autoCorr F 0 * Real.sqrt (∑ k ∈ Finset.range n, RHTower.vonMangoldtAtom k ^ 2)) ^ 2 := by
    have hrw : (autoCorr F 0 * Real.sqrt (∑ k ∈ Finset.range n, RHTower.vonMangoldtAtom k ^ 2)) ^ 2
        = autoCorr F 0 * ((∑ k ∈ Finset.range n, RHTower.vonMangoldtAtom k ^ 2) * autoCorr F 0) := by
      rw [mul_pow, Real.sq_sqrt hdiag]
      ring
    rw [hrw]
    nlinarith [key, h0, hoff]
  have hy : 0 ≤ autoCorr F 0 * Real.sqrt (∑ k ∈ Finset.range n, RHTower.vonMangoldtAtom k ^ 2) :=
    mul_nonneg h0 (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hy]
  exact Real.sqrt_le_sqrt hsq

/-! ### The incidence energy of a pair of spacings -/
/-- The incidence energy of the pair of spacings `(a, b)`:
`A(0) − A(a) − A(b) + (A(a+b) + A(a−b))/2`, a quarter of `‖(1 − T_a)(1 − T_b)F‖²`. It couples the
two spacings through their **product** shift `a + b` and their **ratio** shift `a − b`. -/
def pairIncidenceEnergy (F : ℝ → ℝ) (a b : ℝ) : ℝ :=
  autoCorr F 0 - autoCorr F a - autoCorr F b + (autoCorr F (a + b) + autoCorr F (a - b)) / 2

/-- The double difference `(1 − T_a)(1 − T_b)F` of a test. -/
def doubleDifference (F : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  fun u => (F u - F (u + b)) - (F (u + a) - F (u + (a + b)))

theorem ContCompact.doubleDifference (hF : ContCompact F) (a b : ℝ) :
    ContCompact (doubleDifference F a b) :=
  (hF.sub_nice (hF.translate b)).sub_nice
    ((hF.translate a).sub_nice (hF.translate (a + b)))

/-- The pairing of the double difference with itself is four times the incidence energy. -/
theorem testPairing_doubleDifference (hF : ContCompact F) (a b : ℝ) :
    testPairing (doubleDifference F a b) (doubleDifference F a b) = 4 * pairIncidenceEnergy F a b := by
  have hT : ∀ t : ℝ, ContCompact (fun u => F (u + t)) := fun t => hF.translate t
  have hu : ContCompact (fun u => F u - F (u + b)) := hF.sub_nice (hT b)
  have hv : ContCompact (fun u => F (u + a) - F (u + (a + b))) := (hT a).sub_nice (hT (a + b))
  have q00 : testPairing F F = autoCorr F 0 := testPairing_self_eq_autoCorr_zero F
  have q0b : testPairing F (fun u => F (u + b)) = autoCorr F b := rfl
  have q0a : testPairing F (fun u => F (u + a)) = autoCorr F a := rfl
  have q0ab : testPairing F (fun u => F (u + (a + b))) = autoCorr F (a + b) := rfl
  have qb0 : testPairing (fun u => F (u + b)) F = autoCorr F b := by rw [testPairing_comm]; exact q0b
  have qbb : testPairing (fun u => F (u + b)) (fun u => F (u + b)) = autoCorr F 0 := by
    rw [testPairing_translate F F b]; exact q00
  have qba : testPairing (fun u => F (u + b)) (fun u => F (u + a)) = autoCorr F (a - b) :=
    testPairing_translate_pair F b a
  have qbab : testPairing (fun u => F (u + b)) (fun u => F (u + (a + b))) = autoCorr F a := by
    rw [testPairing_translate_pair F b (a + b), add_sub_cancel_right]
  have qa0 : testPairing (fun u => F (u + a)) F = autoCorr F a := by rw [testPairing_comm]; exact q0a
  have qab0 : testPairing (fun u => F (u + (a + b))) F = autoCorr F (a + b) := by
    rw [testPairing_comm]; exact q0ab
  have qaa : testPairing (fun u => F (u + a)) (fun u => F (u + a)) = autoCorr F 0 := by
    rw [testPairing_translate F F a]; exact q00
  have qaab : testPairing (fun u => F (u + a)) (fun u => F (u + (a + b))) = autoCorr F b := by
    rw [testPairing_translate_pair F a (a + b), add_sub_cancel_left]
  have qabb : testPairing (fun u => F (u + (a + b))) (fun u => F (u + b)) = autoCorr F a := by
    rw [testPairing_translate_pair F (a + b) b, show b - (a + b) = -a by ring, autoCorr_neg]
  have qaba : testPairing (fun u => F (u + (a + b))) (fun u => F (u + a)) = autoCorr F b := by
    rw [testPairing_translate_pair F (a + b) a, show a - (a + b) = -b by ring, autoCorr_neg]
  have qabab : testPairing (fun u => F (u + (a + b))) (fun u => F (u + (a + b))) = autoCorr F 0 := by
    rw [testPairing_translate F F (a + b)]; exact q00
  have qab : testPairing (fun u => F (u + a)) (fun u => F (u + b)) = autoCorr F (a - b) := by
    rw [testPairing_translate_pair F a b, show b - a = -(a - b) by ring, autoCorr_neg]
  show testPairing (fun u => (fun y => F y - F (y + b)) u - (fun y => F (y + a) - F (y + (a + b))) u)
      (fun u => (fun y => F y - F (y + b)) u - (fun y => F (y + a) - F (y + (a + b))) u) = _
  rw [testPairing_sub_sub hu hv hu hv, testPairing_sub_sub hF (hT b) hF (hT b),
    testPairing_sub_sub hF (hT b) (hT a) (hT (a + b)), testPairing_sub_sub (hT a) (hT (a + b)) hF (hT b),
    testPairing_sub_sub (hT a) (hT (a + b)) (hT a) (hT (a + b))]
  simp only [q00, q0b, q0a, q0ab, qb0, qbb, qba, qbab, qa0, qab0, qaa, qaab, qabb, qaba, qabab,
    qab]
  unfold pairIncidenceEnergy
  ring

/-- **The incidence energy of a pair of spacings is nonnegative.** -/
theorem pairIncidenceEnergy_nonneg (hF : Continuous F) (hFc : HasCompactSupport F) (a b : ℝ) :
    0 ≤ pairIncidenceEnergy F a b := by
  have h := testPairing_self_nonneg (doubleDifference F a b)
  rw [testPairing_doubleDifference ⟨hF, hFc⟩ a b] at h
  linarith only [h]

/-! ### The same-prime part of the ratio off-diagonal -/

/-- The same-prime ratio pairs of `p`: the ordered pairs of powers `(p^{i+1}, p^{i+2+d})`, each
weighted by its two atoms and read at the logarithm of their ratio `p^{d+1}`. These are the
off-diagonal Gram entries of the prime side at which the ratio is an integer. -/
def towerRatioPairs (p : ℕ) (F : ℝ → ℝ) : ℝ :=
  ∑' i : ℕ, ∑' d : ℕ,
    RHTower.vonMangoldtAtom (p ^ (i + 1)) * RHTower.vonMangoldtAtom (p ^ (i + 1 + (d + 1)))
      * autoCorr F (((d : ℝ) + 1) * Real.log p)

/-- **The Gram closure at one prime.** The same-prime ratio pairs of `p` are exactly its tower lag
charge with the weight `log² p/(p − 1)`: the off-diagonal of the prime side at integer ratios
closes back onto the towers. -/
theorem towerRatioPairs_eq {p : ℕ} (hp : p.Prime) (F : ℝ → ℝ) :
    towerRatioPairs p F
      = Real.log p ^ 2 / ((p : ℝ) - 1) * geoLagCharge (1 / Real.sqrt p) (Real.log p) F := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hsq : Real.sqrt p ^ 2 = (p : ℝ) := Real.sq_sqrt hp0.le
  have hz2 : (1 / (p : ℝ)) = (1 / Real.sqrt p) ^ 2 := by rw [div_pow, one_pow, hsq]
  have hterm : ∀ i d : ℕ,
      RHTower.vonMangoldtAtom (p ^ (i + 1)) * RHTower.vonMangoldtAtom (p ^ (i + 1 + (d + 1)))
          * autoCorr F (((d : ℝ) + 1) * Real.log p)
        = Real.log p ^ 2 * (1 / (p : ℝ)) ^ (i + 1)
            * ((1 / Real.sqrt p) ^ (d + 1) * autoCorr F (((d : ℝ) + 1) * Real.log p)) := by
    intro i d
    have hexp : i + 1 + (d + 1) = i + d + 1 + 1 := by omega
    rw [hexp, vonMangoldtAtom_prime_pow hp, vonMangoldtAtom_prime_pow hp, hz2, ← pow_mul]
    ring
  have hgeo : ∑' i : ℕ, Real.log p ^ 2 * (1 / (p : ℝ)) ^ (i + 1)
      = Real.log p ^ 2 / ((p : ℝ) - 1) := by
    have h0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have h1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one hp0]; exact hp1
    have e : ∀ i : ℕ, Real.log p ^ 2 * (1 / (p : ℝ)) ^ (i + 1)
        = Real.log p ^ 2 * (1 / (p : ℝ)) * (1 / (p : ℝ)) ^ i := by intro i; ring
    rw [tsum_congr e, tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
    have hne : (p : ℝ) ≠ 0 := ne_of_gt hp0
    field_simp
  rw [towerRatioPairs, tsum_congr fun i => tsum_congr fun d => hterm i d]
  rw [tsum_congr fun i => tsum_mul_left (f := fun d : ℕ =>
      (1 / Real.sqrt p) ^ (d + 1) * autoCorr F (((d : ℝ) + 1) * Real.log p))
      (a := Real.log p ^ 2 * (1 / (p : ℝ)) ^ (i + 1)), tsum_mul_right, hgeo, geoLagCharge]

/-- **The same-prime sector is a bounded sector.** The same-prime ratio pairs of `p` are bounded by
the first-power data of `p`, with the weight `log² p/(p − 1)²`. Since
`Σ_p log² p · √p/(p − 1)²` converges while the prime side itself is of size `√N`, the Gram
off-diagonal of the prime side is carried entirely by its **cross-prime** pairs. -/
theorem towerRatioPairs_le {p : ℕ} {B : ℝ} (hp : p.Prime) (hF : Continuous F) (hB : 0 ≤ B)
    (hsupp : ∀ x, B < |x| → F x = 0) :
    towerRatioPairs p F
      ≤ Real.log p ^ 2 / ((p : ℝ) - 1) ^ 2
        * (autoCorr F 0 + Real.sqrt p * autoCorr F (Real.log p)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hkey := sub_one_mul_towerCharge_le hp hF hB hsupp
  rw [towerCharge_eq_log_mul_geoLagCharge hp] at hkey
  -- divide by `log p > 0`
  have hgeo : ((p : ℝ) - 1) * geoLagCharge (1 / Real.sqrt p) (Real.log p) F
      ≤ autoCorr F 0 + Real.sqrt p * autoCorr F (Real.log p) := by
    have h : Real.log p * (((p : ℝ) - 1) * geoLagCharge (1 / Real.sqrt p) (Real.log p) F)
        ≤ Real.log p * (autoCorr F 0 + Real.sqrt p * autoCorr F (Real.log p)) := by
      calc Real.log p * (((p : ℝ) - 1) * geoLagCharge (1 / Real.sqrt p) (Real.log p) F)
          = ((p : ℝ) - 1) * (Real.log p * geoLagCharge (1 / Real.sqrt p) (Real.log p) F) := by
            ring
        _ ≤ Real.log p * (autoCorr F 0 + Real.sqrt p * autoCorr F (Real.log p)) := hkey
    exact le_of_mul_le_mul_left h hlog
  rw [towerRatioPairs_eq hp]
  have hw : 0 ≤ Real.log p ^ 2 / ((p : ℝ) - 1) := by positivity
  have hfac : Real.log p ^ 2 / ((p : ℝ) - 1) ^ 2
      * (autoCorr F 0 + Real.sqrt p * autoCorr F (Real.log p))
      = Real.log p ^ 2 / ((p : ℝ) - 1)
        * ((autoCorr F 0 + Real.sqrt p * autoCorr F (Real.log p)) / ((p : ℝ) - 1)) := by
    field_simp
  rw [hfac]
  refine mul_le_mul_of_nonneg_left ?_ hw
  rw [le_div_iff₀ (by linarith)]
  linarith only [hgeo]

/-! ### The decorrelation criterion -/

/-- Distinct integers below the horizon `N` have logarithms separated by at least `1/N`: the
cross lags of the prime side avoid the resolution scale of the horizon. -/
theorem one_div_le_abs_log_sub_log {j k N : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) (hjN : j ≤ N)
    (hkN : k ≤ N) (hne : j ≠ k) : 1 / (N : ℝ) ≤ |Real.log k - Real.log j| := by
  have hgap : ∀ u v : ℕ, 1 ≤ v → v < u → u ≤ N → 1 / (N : ℝ) ≤ Real.log u - Real.log v := by
    intro u v hv1 hvu huN
    have hv0 : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv1
    have hu0 : (0 : ℝ) < (u : ℝ) := by exact_mod_cast lt_of_lt_of_le hv1 hvu.le
    have hdiv : Real.log ((v : ℝ) / (u : ℝ)) ≤ (v : ℝ) / (u : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt hv0) (ne_of_gt hu0)] at hdiv
    have hstep : 1 - (v : ℝ) / (u : ℝ) ≤ Real.log u - Real.log v := by linarith
    have hone : (1 : ℝ) ≤ (u : ℝ) - (v : ℝ) := by
      have : (v : ℝ) + 1 ≤ (u : ℝ) := by exact_mod_cast hvu
      linarith
    have huN' : (u : ℝ) ≤ (N : ℝ) := by exact_mod_cast huN
    have h1 : 1 / (N : ℝ) ≤ 1 / (u : ℝ) := by
      rw [div_le_div_iff₀ (by exact_mod_cast lt_of_lt_of_le hu0 huN') hu0]
      linarith
    have h2 : 1 / (u : ℝ) ≤ 1 - (v : ℝ) / (u : ℝ) := by
      rw [div_le_iff₀ hu0, sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hu0)]
      linarith
    linarith
  have hNpos : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  rcases lt_or_gt_of_ne hne with h | h
  · have hgk := hgap k j hj h hkN
    rw [abs_of_nonneg (by linarith)]
    exact hgk
  · have hgj := hgap j k hk h hjN
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact hgj

/-- **The decorrelation criterion.** If the autocorrelation of a test stays below `ρ A(0)` at every
lag of size at least `1/N` — the resolution of the horizon `N` — then

    |Σ_{k ≤ N} Λ(k) k^{−1/2} A(log k)|
      ≤ A(0) · √(Σ_{k ≤ N} Λ(k)²/k + ρ (Σ_{k ≤ N} Λ(k)/√k)²).

The first sum is of size `log² N`, the second of size `N`, so a test decorrelating to
`ρ ≲ log²N/N` beyond the lag `1/N` has an archimedean-size prime side. This is a replacement
hypothesis on the test, proved sufficient: tests that resolve the scale `1/N` are harmless. -/
theorem abs_sum_prime_autoCorr_le_of_decorrelated (hF : Continuous F) (hFc : HasCompactSupport F)
    {N : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdec : ∀ t : ℝ, 1 / (N : ℝ) ≤ |t| → |autoCorr F t| ≤ ρ * autoCorr F 0) :
    |∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k * autoCorr F (Real.log k)|
      ≤ autoCorr F 0 * Real.sqrt (∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k ^ 2
          + ρ * (∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k) ^ 2) := by
  have h0 : 0 ≤ autoCorr F 0 := autoCorr_zero_nonneg hF hFc
  have hatom : ∀ k : ℕ, 0 ≤ RHTower.vonMangoldtAtom k := fun k => by
    simp only [RHTower.vonMangoldtAtom]
    split
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_refl 0
  have hdiag : 0 ≤ ∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hmass : 0 ≤ ∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k :=
    Finset.sum_nonneg fun k _ => hatom k
  -- the correlation form is bounded by the diagonal plus `ρ` times the squared mass
  have hform : ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k
          * autoCorr F (Real.log k - Real.log j)
      ≤ autoCorr F 0 * ((∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k ^ 2)
          + ρ * (∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k) ^ 2) := by
    have hbd : ∀ j ∈ Finset.range (N + 1), ∀ k ∈ Finset.range (N + 1),
        RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k
            * autoCorr F (Real.log k - Real.log j)
          ≤ autoCorr F 0 * (if j = k then RHTower.vonMangoldtAtom j ^ 2
              else ρ * (RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k)) := by
      intro j hj k hk
      have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases hjk : j = k
      · subst hjk
        rw [if_pos rfl, sub_self]
        nlinarith [hatom j, h0]
      · rw [if_neg hjk]
        by_cases hzj : RHTower.vonMangoldtAtom j = 0
        · rw [hzj]
          nlinarith [hatom k, h0, hρ]
        by_cases hzk : RHTower.vonMangoldtAtom k = 0
        · rw [hzk]
          nlinarith [hatom j, h0, hρ]
        have hj2 : 2 ≤ j := by
          by_contra hc
          exact hzj (by simp [RHTower.vonMangoldtAtom, if_neg (by omega : ¬ 2 ≤ j)])
        have hk2 : 2 ≤ k := by
          by_contra hc
          exact hzk (by simp [RHTower.vonMangoldtAtom, if_neg (by omega : ¬ 2 ≤ k)])
        have hlag : 1 / (N : ℝ) ≤ |Real.log k - Real.log j| :=
          one_div_le_abs_log_sub_log (by omega) (by omega) hjN hkN hjk
        have habs := (abs_le.mp (hdec _ hlag)).2
        nlinarith [hatom j, hatom k, mul_nonneg (hatom j) (hatom k)]
    refine le_trans (Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => hbd j hj k hk) ?_
    have hsplit : ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
          autoCorr F 0 * (if j = k then RHTower.vonMangoldtAtom j ^ 2
            else ρ * (RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k))
        ≤ autoCorr F 0 * ((∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k ^ 2)
            + ρ * (∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k) ^ 2) := by
      have hpull : ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
            autoCorr F 0 * (if j = k then RHTower.vonMangoldtAtom j ^ 2
              else ρ * (RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k))
          = autoCorr F 0 * ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
            (if j = k then RHTower.vonMangoldtAtom j ^ 2
              else ρ * (RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
      rw [hpull]
      refine mul_le_mul_of_nonneg_left ?_ h0
      have hrow : ∀ j ∈ Finset.range (N + 1),
          ∑ k ∈ Finset.range (N + 1), (if j = k then RHTower.vonMangoldtAtom j ^ 2
              else ρ * (RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k))
            ≤ RHTower.vonMangoldtAtom j ^ 2
              + ρ * (RHTower.vonMangoldtAtom j
                * ∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k) := by
        intro j hj
        have hle : ∀ k ∈ Finset.range (N + 1),
            (if j = k then RHTower.vonMangoldtAtom j ^ 2
              else ρ * (RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k))
              ≤ (if j = k then RHTower.vonMangoldtAtom j ^ 2 else 0)
                + ρ * (RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k) := by
          intro k _
          by_cases hjk : j = k
          · rw [if_pos hjk, if_pos hjk]
            nlinarith [mul_nonneg (hatom j) (hatom k), hρ]
          · rw [if_neg hjk, if_neg hjk]
            linarith
        calc ∑ k ∈ Finset.range (N + 1), (if j = k then RHTower.vonMangoldtAtom j ^ 2
                else ρ * (RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k))
            ≤ ∑ k ∈ Finset.range (N + 1),
                ((if j = k then RHTower.vonMangoldtAtom j ^ 2 else 0)
                  + ρ * (RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k)) :=
              Finset.sum_le_sum hle
          _ = RHTower.vonMangoldtAtom j ^ 2
                + ρ * (RHTower.vonMangoldtAtom j
                  * ∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k) := by
              rw [Finset.sum_add_distrib, Finset.sum_ite_eq _ _ _, if_pos hj, ← Finset.mul_sum,
                ← Finset.mul_sum]
      calc ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
              (if j = k then RHTower.vonMangoldtAtom j ^ 2
                else ρ * (RHTower.vonMangoldtAtom j * RHTower.vonMangoldtAtom k))
          ≤ ∑ j ∈ Finset.range (N + 1), (RHTower.vonMangoldtAtom j ^ 2
              + ρ * (RHTower.vonMangoldtAtom j
                * ∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k)) :=
            Finset.sum_le_sum hrow
        _ = (∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k ^ 2)
              + ρ * (∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k) ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
            ring
    exact hsplit
  -- combine with the shift-Gram law
  have key := sq_sum_prime_autoCorr_le hF hFc (N + 1)
  have hsq : (∑ k ∈ Finset.range (N + 1),
        RHTower.vonMangoldtAtom k * autoCorr F (Real.log k)) ^ 2
      ≤ (autoCorr F 0 * Real.sqrt ((∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k ^ 2)
          + ρ * (∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k) ^ 2)) ^ 2 := by
    have hrad : 0 ≤ (∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k ^ 2)
        + ρ * (∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k) ^ 2 := by
      have : 0 ≤ ρ * (∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k) ^ 2 :=
        mul_nonneg hρ (sq_nonneg _)
      linarith
    rw [mul_pow, Real.sq_sqrt hrad]
    nlinarith [key, hform, h0]
  have hy : 0 ≤ autoCorr F 0 * Real.sqrt ((∑ k ∈ Finset.range (N + 1),
      RHTower.vonMangoldtAtom k ^ 2)
      + ρ * (∑ k ∈ Finset.range (N + 1), RHTower.vonMangoldtAtom k) ^ 2) :=
    mul_nonneg h0 (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq hy]
  exact Real.sqrt_le_sqrt hsq

/-! ### The archimedean floor of a decorrelating test -/

/-- The autocorrelation of a Lipschitz compactly supported test is Lipschitz, hence continuous. -/
theorem continuous_autoCorr_of_lipschitz (hF : Continuous F) (hFc : HasCompactSupport F) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ a b, |F a - F b| ≤ K * |a - b|) : Continuous (autoCorr F) := by
  have hFn : ContCompact F := ⟨hF, hFc⟩
  have hint : Integrable fun t => |F t| :=
    (hF.abs).integrable_of_hasCompactSupport hFc.abs
  have hc : 0 ≤ K * ∫ t, |F t| := mul_nonneg hK0 (integral_nonneg fun t => abs_nonneg _)
  refine (LipschitzWith.of_dist_le_mul (K := ⟨K * ∫ t, |F t|, hc⟩) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq]
  have h1 : Integrable fun t => F t * F (t + x) :=
    ContCompact.integrable_mul hFn (hFn.translate x)
  have h2 : Integrable fun t => F t * F (t + y) :=
    ContCompact.integrable_mul hFn (hFn.translate y)
  have hsub : autoCorr F x - autoCorr F y = ∫ t, (F t * F (t + x) - F t * F (t + y)) := by
    rw [integral_sub h1 h2]
    rfl
  rw [hsub]
  refine le_trans abs_integral_le_integral_abs ?_
  have hbd : ∀ t, |F t * F (t + x) - F t * F (t + y)| ≤ |F t| * (K * |x - y|) := by
    intro t
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h := hK (t + x) (t + y)
    rwa [show t + x - (t + y) = x - y by ring] at h
  calc (∫ t, |F t * F (t + x) - F t * F (t + y)|) ≤ ∫ t, |F t| * (K * |x - y|) :=
        integral_mono (h1.sub h2).abs (hint.mul_const _) hbd
    _ = (K * ∫ t, |F t|) * |x - y| := by rw [integral_mul_const]; ring

/-- The archimedean band energy of a test on the shifts `[δ, 1]`:
`∫_δ^1 ω(t) ‖F − F(· + t)‖² dt`, the part of the archimedean jump energy carried by the shifts
between the resolution `δ` and the unit scale. -/
def archBandEnergy (δ : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∫ t in Set.Icc δ 1, RHTower.archLevyDensity t * (2 * (autoCorr F 0 - autoCorr F t))

/-- **The archimedean floor of a decorrelating test.** If `|A(t)| ≤ ρ A(0)` at every lag `|t| ≥ δ`
then the archimedean band energy on `[δ, 1]` is at least `e^{−1/2}(1 − ρ) A(0) log(1/δ)`: a test
that decorrelates at the scale `δ` pays a *logarithmic* archimedean energy. At `δ = 1/N` this is
`≍ A(0) log N`, the same order as the decorrelation bound on the prime side, so in the
decorrelating regime the two sides of the critical inequality are commensurable and the comparison
is a question of constants, not of orders. -/
theorem archBandEnergy_ge_of_decorrelated (hF : Continuous F) (hFc : HasCompactSupport F)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ a b, |F a - F b| ≤ K * |a - b|)
    {δ ρ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hρ1 : ρ ≤ 1)
    (hdec : ∀ t : ℝ, δ ≤ |t| → |autoCorr F t| ≤ ρ * autoCorr F 0) :
    Real.exp (-(1 / 2)) * ((1 - ρ) * autoCorr F 0) * Real.log (1 / δ) ≤ archBandEnergy δ F := by
  have h0 : 0 ≤ autoCorr F 0 := autoCorr_zero_nonneg hF hFc
  have hAc : Continuous (autoCorr F) := continuous_autoCorr_of_lipschitz hF hFc hK0 hK
  have hρ0 : 0 ≤ (1 - ρ) * autoCorr F 0 := mul_nonneg (by linarith) h0
  -- the integrand dominates `c/t`
  have hmin : ∀ t ∈ Set.Icc δ 1,
      Real.exp (-(1 / 2)) * ((1 - ρ) * autoCorr F 0) * (1 / t)
        ≤ RHTower.archLevyDensity t * (2 * (autoCorr F 0 - autoCorr F t)) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hδ0 ht.1
    have hω : Real.exp (-(1 / 2)) / (2 * t) ≤ RHTower.archLevyDensity t := by
      unfold RHTower.archLevyDensity
      have hden_pos : 0 < 1 - Real.exp (-2 * t) := by
        have : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        linarith
      have hden_le : 1 - Real.exp (-2 * t) ≤ 2 * t := by
        have h := Real.add_one_le_exp (-2 * t)
        linarith
      have hnum : Real.exp (-(1 / 2)) ≤ Real.exp (-t / 2) :=
        Real.exp_le_exp.mpr (by linarith [ht.2])
      rw [div_le_div_iff₀ (by positivity) hden_pos]
      have h1 : Real.exp (-(1 / 2)) * (1 - Real.exp (-2 * t))
          ≤ Real.exp (-(1 / 2)) * (2 * t) :=
        mul_le_mul_of_nonneg_left hden_le (Real.exp_pos _).le
      have h2 : Real.exp (-(1 / 2)) * (2 * t) ≤ Real.exp (-t / 2) * (2 * t) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      linarith
    have hA : (1 - ρ) * autoCorr F 0 ≤ autoCorr F 0 - autoCorr F t := by
      have h := (abs_le.mp (hdec t (by rw [abs_of_pos ht0]; exact ht.1))).2
      linarith
    have hstep : (Real.exp (-(1 / 2)) / (2 * t)) * (2 * ((1 - ρ) * autoCorr F 0))
        ≤ RHTower.archLevyDensity t * (2 * (autoCorr F 0 - autoCorr F t)) := by
      exact mul_le_mul hω (by linarith) (by linarith) (le_trans (by positivity) hω)
    calc Real.exp (-(1 / 2)) * ((1 - ρ) * autoCorr F 0) * (1 / t)
        = (Real.exp (-(1 / 2)) / (2 * t)) * (2 * ((1 - ρ) * autoCorr F 0)) := by
          field_simp
      _ ≤ _ := hstep
  -- both sides are integrable on the band
  have hωc : ContinuousOn RHTower.archLevyDensity (Set.Icc δ 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_
    have ht0 : 0 < t := lt_of_lt_of_le hδ0 ht.1
    have : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hint1 : IntegrableOn (fun t => Real.exp (-(1 / 2)) * ((1 - ρ) * autoCorr F 0) * (1 / t))
      (Set.Icc δ 1) := by
    refine ContinuousOn.integrableOn_Icc (ContinuousOn.mul continuousOn_const ?_)
    exact ContinuousOn.div continuousOn_const continuousOn_id fun t ht =>
      ne_of_gt (lt_of_lt_of_le hδ0 ht.1)
  have hint2 : IntegrableOn
      (fun t => RHTower.archLevyDensity t * (2 * (autoCorr F 0 - autoCorr F t)))
      (Set.Icc δ 1) :=
    ContinuousOn.integrableOn_Icc (hωc.mul (by fun_prop))
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Icc hmin
  -- evaluate the minorant
  have heval : ∫ t in Set.Icc δ 1, Real.exp (-(1 / 2)) * ((1 - ρ) * autoCorr F 0) * (1 / t)
      = Real.exp (-(1 / 2)) * ((1 - ρ) * autoCorr F 0) * Real.log (1 / δ) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hδ1,
      intervalIntegral.integral_const_mul, integral_one_div (by
        rw [Set.uIcc_of_le hδ1]
        exact fun h => absurd h.1 (not_le.mpr hδ0))]
  rw [archBandEnergy, ← heval]
  exact hmono

/-! ### The two-shift coupling law with tunable weights -/

/-- The weighted double difference `(1 − λT_a)(1 − μT_b)F` of a test. -/
def weightedDoubleDifference (F : ℝ → ℝ) (lam mu a b : ℝ) : ℝ → ℝ :=
  fun u => (F u - mu * F (u + b)) - lam * (F (u + a) - mu * F (u + (a + b)))

/-- **The two-shift coupling law.** For every pair of shifts and every pair of weights,

    2λ(1+μ²) A(a) + 2μ(1+λ²) A(b)
      ≤ (1+λ²)(1+μ²) A(0) + 2λμ (A(a+b) + A(a−b)).

The two payers of the charges at `a` and `b` are the charges at their **product** shift `a + b` and
their **ratio** shift `a − b`, with the tunable edge weight `2λμ`; at `λ = μ = 1` this is the
nonnegativity of the pair incidence energy. For `a = log p`, `b = log q` it is the coupling law
between the towers of two primes, with weights the allocation may choose per pair. -/
theorem two_shift_coupling (hF : Continuous F) (hFc : HasCompactSupport F) (lam mu a b : ℝ) :
    2 * lam * (1 + mu ^ 2) * autoCorr F a + 2 * mu * (1 + lam ^ 2) * autoCorr F b
      ≤ (1 + lam ^ 2) * (1 + mu ^ 2) * autoCorr F 0
        + 2 * lam * mu * (autoCorr F (a + b) + autoCorr F (a - b)) := by
  have hFn : ContCompact F := ⟨hF, hFc⟩
  have hT : ∀ t : ℝ, ContCompact (fun u => F (u + t)) := fun t => hFn.translate t
  have hu : ContCompact (fun u => F u - mu * F (u + b)) :=
    hFn.sub_nice (ContCompact.const_mul_nice mu (hT b))
  have hv : ContCompact (fun u => F (u + a) - mu * F (u + (a + b))) :=
    (hT a).sub_nice (ContCompact.const_mul_nice mu (hT (a + b)))
  -- the nine base pairings
  have q00 : testPairing F F = autoCorr F 0 := testPairing_self_eq_autoCorr_zero F
  have q0b : testPairing F (fun u => F (u + b)) = autoCorr F b := rfl
  have q0a : testPairing F (fun u => F (u + a)) = autoCorr F a := rfl
  have q0ab : testPairing F (fun u => F (u + (a + b))) = autoCorr F (a + b) := rfl
  have qb0 : testPairing (fun u => F (u + b)) F = autoCorr F b := by
    rw [testPairing_comm]; exact q0b
  have qbb : testPairing (fun u => F (u + b)) (fun u => F (u + b)) = autoCorr F 0 := by
    rw [testPairing_translate F F b]; exact q00
  have qba : testPairing (fun u => F (u + b)) (fun u => F (u + a)) = autoCorr F (a - b) :=
    testPairing_translate_pair F b a
  have qbab : testPairing (fun u => F (u + b)) (fun u => F (u + (a + b))) = autoCorr F a := by
    rw [testPairing_translate_pair F b (a + b), add_sub_cancel_right]
  have qa0 : testPairing (fun u => F (u + a)) F = autoCorr F a := by
    rw [testPairing_comm]; exact q0a
  have qab0 : testPairing (fun u => F (u + (a + b))) F = autoCorr F (a + b) := by
    rw [testPairing_comm]; exact q0ab
  have qaa : testPairing (fun u => F (u + a)) (fun u => F (u + a)) = autoCorr F 0 := by
    rw [testPairing_translate F F a]; exact q00
  have qaab : testPairing (fun u => F (u + a)) (fun u => F (u + (a + b))) = autoCorr F b := by
    rw [testPairing_translate_pair F a (a + b), add_sub_cancel_left]
  have qabb : testPairing (fun u => F (u + (a + b))) (fun u => F (u + b)) = autoCorr F a := by
    rw [testPairing_translate_pair F (a + b) b, show b - (a + b) = -a by ring, autoCorr_neg]
  have qaba : testPairing (fun u => F (u + (a + b))) (fun u => F (u + a)) = autoCorr F b := by
    rw [testPairing_translate_pair F (a + b) a, show a - (a + b) = -b by ring, autoCorr_neg]
  have qabab : testPairing (fun u => F (u + (a + b))) (fun u => F (u + (a + b)))
      = autoCorr F 0 := by
    rw [testPairing_translate F F (a + b)]; exact q00
  have qab : testPairing (fun u => F (u + a)) (fun u => F (u + b)) = autoCorr F (a - b) := by
    rw [testPairing_translate_pair F a b, show b - a = -(a - b) by ring, autoCorr_neg]
  -- expand the square of the weighted double difference
  have hsq : 0 ≤ testPairing
      (fun u => (F u - mu * F (u + b)) - lam * (F (u + a) - mu * F (u + (a + b))))
      (fun u => (F u - mu * F (u + b)) - lam * (F (u + a) - mu * F (u + (a + b)))) :=
    testPairing_self_nonneg (weightedDoubleDifference F lam mu a b)
  rw [testPairing_sub_smul_sub_smul hu hv hu hv lam,
    testPairing_sub_smul_sub_smul hFn (hT b) hFn (hT b) mu,
    testPairing_sub_smul_sub_smul hFn (hT b) (hT a) (hT (a + b)) mu,
    testPairing_sub_smul_sub_smul (hT a) (hT (a + b)) hFn (hT b) mu,
    testPairing_sub_smul_sub_smul (hT a) (hT (a + b)) (hT a) (hT (a + b)) mu] at hsq
  simp only [q00, q0b, q0a, q0ab, qb0, qbb, qba, qbab, qa0, qab0, qaa, qaab, qabb, qaba, qabab,
    qab] at hsq
  nlinarith [hsq]

/-- **The coupling identity.** The slack of the one-parameter coupling law splits exactly into the
shift defect at `a` and the pair incidence energy of `(a, b)`:

    A(0) + θ(A(a+b) + A(a−b)) − A(a) − 2θ A(b)
      = (1 − 2θ)(A(0) − A(a)) + 2θ · pairIncidenceEnergy F a b.

In symbol form the slack is `(1 − cos aξ)(1 − 2θ cos bξ)`, whose factorisation this is. -/
theorem autoCorr_coupling_identity (F : ℝ → ℝ) (θ a b : ℝ) :
    autoCorr F 0 + θ * (autoCorr F (a + b) + autoCorr F (a - b))
        - autoCorr F a - 2 * θ * autoCorr F b
      = (1 - 2 * θ) * (autoCorr F 0 - autoCorr F a)
        + 2 * θ * pairIncidenceEnergy F a b := by
  unfold pairIncidenceEnergy
  ring

/-- **The sharp coupling law of two shifts.** For every `θ ∈ [0, ½]`,

    A(a) + 2θ A(b) ≤ A(0) + θ (A(a+b) + A(a−b)) :

the charges at two shifts are paid by the mass and, with edge weight `θ ≤ ½`, by the charges at
their **product** shift `a + b` and their **ratio** shift `a − b`. The range `θ ≤ ½` is exact: the
slack is `(1 − cos aξ)(1 − 2θ cos bξ)` in symbol form. -/
theorem autoCorr_coupling_le (hF : Continuous F) (hFc : HasCompactSupport F) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1 / 2) (a b : ℝ) :
    autoCorr F a + 2 * θ * autoCorr F b
      ≤ autoCorr F 0 + θ * (autoCorr F (a + b) + autoCorr F (a - b)) := by
  have hdef : autoCorr F a ≤ autoCorr F 0 :=
    le_trans (le_abs_self _) (abs_autoCorr_le_autoCorr_zero hF hFc a)
  have hpair : 0 ≤ pairIncidenceEnergy F a b := pairIncidenceEnergy_nonneg hF hFc a b
  have hid := autoCorr_coupling_identity F θ a b
  nlinarith [hid, hdef, hpair, hθ0, hθ1]

end GaloisForLFunctions.ArithmeticIncidencePositivity
