import GaloisForLFunctions.RHTower.WeilFiniteSupportRigidity

/-!
# Weil-cone rigidity for log-summable deviations

**Theorem** (`eq_zero_of_positiveDefinite_neg_nullPotential_of_logSummable`). Let `v : ℕ → ℝ` with
`v(0) = v(1) = 0`, `|v(n)| ≤ 2 log n + A`, and `Σ_n |v(n)|(1 + log n)^{−J} < ∞` for some `J`. If
`−ψ_v` (or `ψ_v`) is positive definite, then `v = 0`.

**Corollary** (`eq_vonMangoldt_of_weilPositiveFull_of_logSummable`). A full-cone Weil-positive `lam`
with `Σ_n |lam(n) − Λ(n)| n^{−1/2}(1 + log n)^{−J} < ∞` equals `Λ`. This contains every
sparse-support rigidity class: lacunary supports of every ratio, finite unions of geometric
progressions, finitely generated semigroups, and the log-square-summable class.

**Proof.** Fix `n₀` and truncate the Euler weight of the `|ζ|²` notch at the primes `P = P_y ≤ y`.
Every `n` splits as `n = n_P n_R` (`smoothPart`, `roughPart`), and the twists of the notch are the
coprime ratios `h(b) n_R / k(b)`. The Poisson cancellation over `P` leaves the main term
`Π_{p≤y}(1 − 1/p) ∫ ω log t · (ε Σ_{n_P = n₀} v(n) n_R^{−1/2} + 2 Σ_{n_P = 1} v(n) n^{−1/2})`. The
errors of MUST-570 give that this bracket is `≤ 0` for both signs. Every nontrivial `P_y`-rough
number exceeds `y`, so the bracket tends to `ε v(n₀)` as `y → ∞`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilLogSummable

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport

/-! ## Smooth and rough parts -/

/-- The primes up to `y`. -/
def primesUpTo (y : ℕ) : Finset ℕ := (Finset.range (y + 1)).filter Nat.Prime

theorem mem_primesUpTo {y p : ℕ} : p ∈ primesUpTo y ↔ p ≤ y ∧ p.Prime := by
  unfold primesUpTo
  rw [Finset.mem_filter, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

theorem prime_of_mem_primesUpTo {y : ℕ} : ∀ p ∈ primesUpTo y, p.Prime :=
  fun _ hp => (mem_primesUpTo.mp hp).2

variable {P : Finset ℕ}

/-- The `P`-part `n_P = Π_{p∈P} p^{v_p(n)}`. -/
def smoothPart (P : Finset ℕ) (n : ℕ) : ℕ := ∏ p : P, (p : ℕ) ^ n.factorization p

/-- The `P`-rough part `n_R = n / n_P`. -/
def roughPart (P : Finset ℕ) (n : ℕ) : ℕ := n / smoothPart P n

theorem vecNum_vecOf_eq (n : ℕ) : vecNum (vecOf P n) = smoothPart P n := by
  unfold vecNum vecOf smoothPart
  simp only [Int.toNat_natCast]

theorem smoothPart_pos (hP : ∀ p ∈ P, p.Prime) (n : ℕ) : 0 < smoothPart P n :=
  Finset.prod_pos fun p _ => pow_pos (hP p p.2).pos _

theorem smoothPart_dvd (n : ℕ) (hn : n ≠ 0) : smoothPart P n ∣ n := by
  classical
  unfold smoothPart
  rw [Finset.prod_coe_sort P (fun p => p ^ n.factorization p)]
  have hfilt : ∏ p ∈ P, p ^ n.factorization p =
      ∏ p ∈ P.filter (· ∈ n.primeFactors), p ^ n.factorization p := by
    rw [Finset.prod_filter_of_ne]
    intro p _ hne
    by_contra hmem
    apply hne
    rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hmem
    rw [hmem, pow_zero]
  rw [hfilt]
  calc ∏ p ∈ P.filter (· ∈ n.primeFactors), p ^ n.factorization p
      ∣ ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
        Finset.prod_dvd_prod_of_subset _ _ _ (fun p hp => (Finset.mem_filter.mp hp).2)
    _ = n := by
        rw [← Nat.support_factorization]
        exact Nat.prod_factorization_pow_eq_self hn

theorem smoothPart_mul_roughPart (n : ℕ) (hn : n ≠ 0) : smoothPart P n * roughPart P n = n :=
  Nat.mul_div_cancel' (smoothPart_dvd n hn)

theorem roughPart_pos {n : ℕ} (hn : n ≠ 0) : 0 < roughPart P n := by
  have h := smoothPart_mul_roughPart (P := P) n hn
  rcases Nat.eq_zero_or_pos (roughPart P n) with h0 | h0
  · rw [h0, mul_zero] at h
    exact absurd h.symm hn
  · exact h0

theorem not_dvd_roughPart (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0) {p : ℕ} (hp : p ∈ P) :
    ¬ p ∣ roughPart P n := by
  intro hd
  have hpow : p ^ n.factorization p ∣ smoothPart P n := by
    unfold smoothPart
    exact Finset.dvd_prod_of_mem (fun q : P => (q : ℕ) ^ n.factorization q)
      (Finset.mem_univ (⟨p, hp⟩ : P))
  have : p ^ (n.factorization p + 1) ∣ n := by
    calc p ^ (n.factorization p + 1) = p ^ n.factorization p * p := pow_succ _ _
      _ ∣ smoothPart P n * roughPart P n := mul_dvd_mul hpow hd
      _ = n := smoothPart_mul_roughPart n hn
  exact Nat.pow_succ_factorization_not_dvd hn (hP p hp) this

theorem factorization_roughPart_eq_zero (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0) {p : ℕ}
    (hp : p ∈ P) : (roughPart P n).factorization p = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (not_dvd_roughPart hP hn hp)

theorem log_eq_smooth_add_rough (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0) :
    Real.log n = Real.log (smoothPart P n) + Real.log (roughPart P n) := by
  have hs : (0 : ℝ) < smoothPart P n := by exact_mod_cast smoothPart_pos hP n
  have hr : (0 : ℝ) < roughPart P n := by exact_mod_cast roughPart_pos hn
  rw [← Real.log_mul hs.ne' hr.ne', ← Nat.cast_mul, smoothPart_mul_roughPart n hn]

theorem vecFreq_vecOf_eq_log_smoothPart (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    vecFreq (vecOf P n) = Real.log (smoothPart P n) := by
  rw [vecFreq_eq hP, vecNum_vecOf_eq, vecDen_vecOf, Nat.cast_one, Real.log_one, sub_zero]

theorem inv_sqrt_smoothPart_eq (n : ℕ) :
    (Real.sqrt (smoothPart P n))⁻¹ = ∏ p : P, primeHalf p ^ n.factorization p := by
  have h := inv_sqrt_vecNum_mul_vecDen (vecOf P n)
  rw [vecNum_vecOf_eq, vecDen_vecOf, Nat.cast_one, mul_one] at h
  rw [h]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp [vecOf]

/-- A nontrivial `P_y`-rough number exceeds `y`. -/
theorem lt_of_vecOf_eq_zero {y n : ℕ} (hn : 2 ≤ n) (h0 : vecOf (primesUpTo y) n = 0) : y < n := by
  set q := n.minFac with hq
  have hqp : q.Prime := Nat.minFac_prime (by omega)
  have hqn : q ∣ n := Nat.minFac_dvd n
  have hqle : q ≤ n := Nat.minFac_le (by omega)
  by_contra hle
  push Not at hle
  have hmem : q ∈ primesUpTo y := mem_primesUpTo.mpr ⟨by omega, hqp⟩
  have h1 := congrFun h0 ⟨q, hmem⟩
  simp only [vecOf, Pi.zero_apply, Nat.cast_eq_zero] at h1
  have hpos : 0 < n.factorization q := hqp.factorization_pos_of_dvd (by omega) hqn
  omega

/-! ## Fibers of the truncation -/

theorem smoothPart_eq_of_vecOf_eq {n m : ℕ} (h : vecOf P n = vecOf P m) :
    smoothPart P n = smoothPart P m := by
  unfold smoothPart
  refine Finset.prod_congr rfl fun p _ => ?_
  have := congrFun h p
  simp only [vecOf, Nat.cast_inj] at this
  rw [this]

theorem smoothPart_of_smooth {n : ℕ} (hn : IsSmoothOver P n) : smoothPart P n = n :=
  prod_pow_factorization_eq hn

theorem smoothPart_eq_one {n : ℕ} (h : vecOf P n = 0) : smoothPart P n = 1 := by
  unfold smoothPart
  refine Finset.prod_eq_one fun p _ => ?_
  have := congrFun h p
  simp only [vecOf, Pi.zero_apply, Nat.cast_eq_zero] at this
  rw [this, pow_zero]

theorem roughPart_eq_self {n : ℕ} (h : vecOf P n = 0) : roughPart P n = n := by
  unfold roughPart
  rw [smoothPart_eq_one h, Nat.div_one]

theorem vecOf_roughPart (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0) :
    vecOf P (roughPart P n) = 0 := by
  funext p
  simp [vecOf, factorization_roughPart_eq_zero hP hn p.2]

theorem eq_mul_roughPart {n n₀ : ℕ} (hn : n ≠ 0)
    (hn₀ : IsSmoothOver P n₀) (h : vecOf P n = vecOf P n₀) : n = n₀ * roughPart P n := by
  have := smoothPart_mul_roughPart (P := P) n hn
  rw [smoothPart_eq_of_vecOf_eq h, smoothPart_of_smooth hn₀] at this
  exact this.symm

/-! ## The main term at a general twist -/

/-- The truncated Poisson cancellation at a general `n`:
`Σ_{j,c} e_j(−ε) E(c) Π_p s_p^{|b_p|} = ((1 + ε²)[a(n) = 0] + ε[a(n) = a(n₀)]) Π_p (1 − s_p²)`. -/
theorem sum_modeCoeff_mul_weight_general {n n₀ : ℕ} (hn₀ : IsSmoothOver P n₀) (ε : ℝ) :
    ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        modeCoeff ε j c * ∏ p : P, primeHalf p ^ ((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs =
      ((1 + ε ^ 2) * (if vecOf P n = 0 then 1 else 0) +
        ε * (if vecOf P n = vecOf P n₀ then 1 else 0)) * ∏ p : P, (1 - primeHalf p ^ 2) := by
  classical
  have hj : ∀ j : ℤ, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
      modeCoeff ε j c * ∏ p : P, primeHalf p ^ ((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs =
      bohrCoeff (-ε) j * (if vecOf P n - j • vecOf P n₀ = 0 then
        ∏ p : P, (1 - primeHalf p ^ 2) else 0) := by
    intro j
    simp_rw [modeCoeff, mul_assoc, ← Finset.mul_sum]
    congr 1
    rw [← sum_bohrVec_mul_prod_pow (fun p : P => primeHalf p) (vecOf P n - j • vecOf P n₀)]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    congr 2
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hj j), sum_bohrModes]
  have hm1 : ¬ (vecOf P n - (-1 : ℤ) • vecOf P n₀ = 0) := by
    intro h
    apply vecOf_ne_zero hn₀
    funext p
    have h1 := congrFun h p
    have h2 := vecOf_nonneg P n p
    have h3 := vecOf_nonneg P n₀ p
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    simp only [Pi.zero_apply]
    linarith
  have h0 : (vecOf P n - (0 : ℤ) • vecOf P n₀ = 0) ↔ vecOf P n = 0 := by
    rw [zero_smul, sub_zero]
  have h1 : (vecOf P n - (1 : ℤ) • vecOf P n₀ = 0) ↔ vecOf P n = vecOf P n₀ := by
    rw [one_smul, sub_eq_zero]
  have b0 : bohrCoeff (-ε) 0 = 1 + ε ^ 2 := by rw [bohrCoeff, if_pos rfl, neg_sq]
  have b1 : bohrCoeff (-ε) 1 = ε := by rw [bohrCoeff, if_neg (by decide), neg_neg]
  rw [if_neg hm1, b0, b1]
  simp only [h0, h1]
  split_ifs <;> ring

theorem coprime_roughPart_vecDen (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0) (b : P → ℤ) :
    Nat.Coprime (roughPart P n) (vecDen b) := by
  unfold vecDen
  refine Nat.Coprime.prod_right fun p _ => Nat.Coprime.pow_right _ ?_
  exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hP p p.2)).mpr
    (not_dvd_roughPart hP hn p.2)))

/-- **The weighted moment at a general twist**: main term plus the envelopes of the modes. -/
theorem exists_norm_weightedMoment_sub_main_le_general (hP : ∀ p ∈ P, p.Prime) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L δ : ℝ}, 16 ≤ L → 0 < δ → δ ≤ 1 / 4 → ∀ (ε : ℝ) {n n₀ : ℕ},
      n ≠ 0 → IsSmoothOver P n₀ →
      ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
          ((((1 + ε ^ 2) * (if vecOf P n = 0 then 1 else 0) +
            ε * (if vecOf P n = vecOf P n₀ then 1 else 0)) * ∏ p : P, (1 - primeHalf p ^ 2)) *
              (Real.sqrt (roughPart P n))⁻¹ : ℝ) * logWindow L‖ ≤
        ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
          |modeCoeff ε j c| * hkEnvelope C L δ K
            (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
            (vecDen (vecOf P n - (j • vecOf P n₀ + c))) := by
  classical
  obtain ⟨C, hC, hmain⟩ := exists_norm_twistedMoment_hk_sub_le K
  refine ⟨C, hC, fun {L δ} hL hδ hδ4 ε {n n₀} hn hn₀ => ?_⟩
  have hL0 : 0 < L := by linarith
  set r := roughPart P n with hr
  have hr0 : 0 < r := roughPart_pos hn
  set b : ℤ → (P → ℤ) → (P → ℤ) := fun j c => vecOf P n - (j • vecOf P n₀ + c) with hb
  have hfreq : ∀ j c, Real.log n - modeFreq n₀ j c =
      Real.log ((vecNum (b j c) * r : ℕ) : ℝ) - Real.log (vecDen (b j c)) := by
    intro j c
    have hnum : (0 : ℝ) < vecNum (b j c) := by exact_mod_cast vecNum_pos hP (b j c)
    have hrr : (0 : ℝ) < r := by exact_mod_cast hr0
    rw [Nat.cast_mul, Real.log_mul hnum.ne' hrr.ne', log_eq_smooth_add_rough hP hn,
      ← vecFreq_vecOf_eq_log_smoothPart hP, modeFreq_eq hn₀.2]
    have := vecFreq_eq hP (b j c)
    rw [hb] at this ⊢
    simp only at this ⊢
    rw [vecFreq_sub] at this
    linarith
  have hweight : ∀ j c, (Real.sqrt (((vecNum (b j c) * r : ℕ) : ℝ) * vecDen (b j c)))⁻¹ =
      (∏ p : P, primeHalf p ^ ((b j c) p).natAbs) * (Real.sqrt r)⁻¹ := by
    intro j c
    rw [← inv_sqrt_vecNum_mul_vecDen (b j c), ← mul_inv, ← Real.sqrt_mul (by positivity)]
    congr 2
    push_cast
    ring
  rw [weightedMoment_notchWeight_eq hL0]
  simp_rw [hfreq]
  have hsum := sum_modeCoeff_mul_weight_general (n := n) hn₀ ε
  have hmainC : ((((1 + ε ^ 2) * (if vecOf P n = 0 then 1 else 0) +
      ε * (if vecOf P n = vecOf P n₀ then 1 else 0)) * ∏ p : P, (1 - primeHalf p ^ 2)) *
        (Real.sqrt r)⁻¹ : ℝ) * logWindow L =
      ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        (modeCoeff ε j c : ℂ) *
          ((((Real.sqrt (((vecNum (b j c) * r : ℕ) : ℝ) * vecDen (b j c)))⁻¹ : ℝ) : ℂ) *
            logWindow L) := by
    rw [← hsum]
    simp_rw [hweight]
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [hmainC, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcop : Nat.Coprime (vecNum (b j c) * r) (vecDen (b j c)) :=
    Nat.Coprime.mul_left (coprime_vecNum_vecDen hP (b j c)) (coprime_roughPart_vecDen hP hn (b j c))
  have h := hmain hL hδ hδ4 (Nat.mul_pos (vecNum_pos hP (b j c)) hr0) (vecDen_pos hP (b j c)) hcop
  push_cast at h ⊢
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-! ## Envelopes at a general twist -/

theorem sqrt_smooth_mul_rough {n : ℕ} (hn : n ≠ 0) :
    Real.sqrt (smoothPart P n) * Real.sqrt (roughPart P n) = Real.sqrt n := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Nat.cast_mul, smoothPart_mul_roughPart n hn]

/-- The envelope of a mode twist at a general `n ≠ 0`. -/
theorem hkEnvelope_mode_le (hP : ∀ p ∈ P, p.Prime) {C L δ : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hδ : 0 < δ) (K : ℕ) {n n₀ : ℕ} (hn : n ≠ 0) {j : ℤ} (hj : j ∈ bohrModes)
    {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    hkEnvelope C L δ K (vecNum (vecOf P n - (j • vecOf P n₀ + c)) * roughPart P n)
        (vecDen (vecOf P n - (j • vecOf P n₀ + c))) ≤
      2 * L * Real.sqrt (twistBound P n₀) * (C + 2 * Real.log (twistBound P n₀) + 2) *
          ((1 + Real.log n) * (Real.sqrt n)⁻¹) +
        C * (24 * δ * (twistBound P n₀ : ℝ) * L * Real.sqrt L + L ^ 2 / (L * δ) ^ K +
          L ^ 2 * Real.exp (-(L ^ 2) / 32)) := by
  set b := vecOf P n - (j • vecOf P n₀ + c) with hb
  set r := roughPart P n with hr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast roughPart_pos hn
  have hs0 : (0 : ℝ) < smoothPart P n := by exact_mod_cast smoothPart_pos hP n
  have hw := weight_mode_le_prod hP hj hc (n := n) (n₀ := n₀)
  have hlog := log_mode_norm_le_prod hP hj hc (n := n) (n₀ := n₀)
  have hden := vecDen_mode_le hP hj hc (n := n) (n₀ := n₀)
  have hK1 : (1 : ℝ) ≤ twistBound P n₀ := by exact_mod_cast twistBound_pos hP n₀
  have hlogK : 0 ≤ Real.log (twistBound P n₀) := Real.log_nonneg hK1
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hN1 : (1 : ℝ) ≤ (vecNum b : ℝ) * vecDen b := by
    have h1 : (1 : ℝ) ≤ vecNum b := by exact_mod_cast vecNum_pos hP b
    have h2 : (1 : ℝ) ≤ vecDen b := by exact_mod_cast vecDen_pos hP b
    nlinarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast roughPart_pos hn
  have hsplitN : (((vecNum b * r : ℕ) : ℝ) * vecDen b) = ((vecNum b : ℝ) * vecDen b) * r := by
    push_cast; ring
  have hwN : (Real.sqrt (((vecNum b * r : ℕ) : ℝ) * vecDen b))⁻¹ =
      (∏ p : P, primeHalf p ^ (b p).natAbs) * (Real.sqrt r)⁻¹ := by
    rw [hsplitN, Real.sqrt_mul (by positivity), mul_inv, inv_sqrt_vecNum_mul_vecDen b]
  have hw' : (Real.sqrt (((vecNum b * r : ℕ) : ℝ) * vecDen b))⁻¹ ≤
      Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹ := by
    rw [hwN, ← sqrt_smooth_mul_rough hn, mul_inv, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hw (by positivity)
  have hlog' : Real.log (((vecNum b * r : ℕ) : ℝ) * vecDen b) ≤
      Real.log n + Real.log (twistBound P n₀) := by
    rw [hsplitN, Real.log_mul (by positivity) hr0.ne', log_eq_smooth_add_rough hP hn]
    unfold smoothPart at hs0 ⊢
    linarith
  have hlogN : 0 ≤ Real.log (((vecNum b * r : ℕ) : ℝ) * vecDen b) := by
    rw [hsplitN]
    exact Real.log_nonneg (by nlinarith)
  unfold hkEnvelope
  apply add_le_add
  · calc (Real.sqrt (((vecNum b * r : ℕ) : ℝ) * vecDen b))⁻¹ *
          (2 * L * (C + 2 * Real.log (((vecNum b * r : ℕ) : ℝ) * vecDen b)))
        ≤ (Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹) *
            (2 * L * (C + 2 * (Real.log n + Real.log (twistBound P n₀)))) := by
          apply mul_le_mul hw' _ (by positivity) (by positivity)
          gcongr
      _ ≤ 2 * L * Real.sqrt (twistBound P n₀) * (C + 2 * Real.log (twistBound P n₀) + 2) *
            ((1 + Real.log n) * (Real.sqrt n)⁻¹) := by
          have hfac : C + 2 * (Real.log n + Real.log (twistBound P n₀)) ≤
              (C + 2 * Real.log (twistBound P n₀) + 2) * (1 + Real.log n) := by nlinarith
          have hpos : 0 ≤ Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹ * (2 * L) := by
            positivity
          calc (Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹) *
                (2 * L * (C + 2 * (Real.log n + Real.log (twistBound P n₀))))
              = (Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹ * (2 * L)) *
                  (C + 2 * (Real.log n + Real.log (twistBound P n₀))) := by ring
            _ ≤ (Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹ * (2 * L)) *
                  ((C + 2 * Real.log (twistBound P n₀) + 2) * (1 + Real.log n)) :=
                mul_le_mul_of_nonneg_left hfac hpos
            _ = _ := by ring
  · apply mul_le_mul_of_nonneg_left _ hC
    gcongr

/-! ## Window bounds and the main-term tail -/

/-- `‖∫ ω(t) log t dt‖ ≤ 2L(log L + 2)`. -/
theorem norm_logWindow_le {L : ℝ} (hL : 2 ≤ L) : ‖logWindow L‖ ≤ 2 * L * (Real.log L + 2) := by
  have hL0 : 0 < L := by linarith
  have h := norm_integral_notchWindow_mul_cexp_le_trivial hL0 (G := fun t => (Real.log t : ℂ))
    (A := Real.log L + 2) (ξ := 0) (fun t ht => by
      have ht0 : 0 < t := by linarith [ht.1]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith [ht.1]))]
      have h1 : Real.log t ≤ Real.log (5 * L / 2) := Real.log_le_log ht0 ht.2
      have h2 : Real.log (5 * L / 2) = Real.log L + Real.log (5 / 2) := by
        rw [show 5 * L / 2 = L * (5 / 2) by ring, Real.log_mul hL0.ne' (by norm_num)]
      have h3 : Real.log (5 / 2 : ℝ) ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 2 by norm_num)
        linarith
      linarith)
  unfold logWindow
  simpa using h

/-- For `log n > M`: `n^{−1/2} ≤ e^{−M/4} C_J (1 + log n)^{−J}`. -/
theorem inv_sqrt_le_of_log_gt (J : ℕ) {M : ℝ} {n : ℕ} (hn : M < Real.log n) :
    (Real.sqrt n)⁻¹ ≤ Real.exp (-(M / 4)) * ((J.factorial * 4 ^ J * Real.exp (1 / 4)) *
      ((1 + Real.log n) ^ J)⁻¹) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp only [Nat.cast_zero, Real.sqrt_zero, inv_zero]
    positivity
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  set x := Real.log n with hx
  have hx0 : 0 ≤ x := Real.log_natCast_nonneg n
  have hsq : (Real.sqrt n)⁻¹ = Real.exp (-(x / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0', ← Real.exp_neg, hx]
    ring_nf
  rw [hsq]
  have h := Real.pow_div_factorial_le_exp (x := (1 + x) / 4) (by positivity) J
  have hf : (0 : ℝ) < J.factorial := by exact_mod_cast J.factorial_pos
  rw [div_le_iff₀ hf, div_pow, div_le_iff₀ (by positivity)] at h
  have hp : 0 < (1 + x) ^ J := by positivity
  rw [← div_eq_mul_inv, mul_div_assoc', le_div_iff₀ hp]
  calc Real.exp (-(x / 2)) * (1 + x) ^ J
      ≤ Real.exp (-(x / 2)) * (Real.exp ((1 + x) / 4) * J.factorial * 4 ^ J) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = Real.exp (-(x / 4)) * (J.factorial * 4 ^ J * Real.exp (1 / 4)) := by
        rw [show Real.exp (-(x / 2)) * (Real.exp ((1 + x) / 4) * J.factorial * 4 ^ J) =
          (Real.exp (-(x / 2)) * Real.exp ((1 + x) / 4)) * (J.factorial * 4 ^ J) by ring,
          ← Real.exp_add, show -(x / 2) + (1 + x) / 4 = -(x / 4) + 1 / 4 by ring, Real.exp_add]
        ring
    _ ≤ Real.exp (-(M / 4)) * (J.factorial * 4 ^ J * Real.exp (1 / 4)) := by
        gcongr

/-! ## The key inequality at a fixed truncation -/

/-- The truncated main coefficient `((1 + ε²)[a(n) = 0] + ε[a(n) = a(n₀)]) n_R^{−1/2}`. -/
def mainWeight (P : Finset ℕ) (ε : ℝ) (n₀ n : ℕ) : ℝ :=
  ((1 + ε ^ 2) * (if vecOf P n = 0 then 1 else 0) +
    ε * (if vecOf P n = vecOf P n₀ then 1 else 0)) * (Real.sqrt (roughPart P n))⁻¹

theorem abs_mainWeight_le {ε : ℝ} (hε : |ε| ≤ 1) {n₀ n : ℕ}
    (hn₀ : IsSmoothOver P n₀) (hn : n ≠ 0) :
    |mainWeight P ε n₀ n| ≤ 3 * Real.sqrt n₀ * (Real.sqrt n)⁻¹ := by
  have hs1 : 1 ≤ Real.sqrt n₀ := Real.one_le_sqrt.mpr (by exact_mod_cast (by have := hn₀.1; omega : 1 ≤ n₀))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith [abs_nonneg ε, sq_abs ε]
  unfold mainWeight
  by_cases h0 : vecOf P n = 0
  · have hne : vecOf P n ≠ vecOf P n₀ := by rw [h0]; exact (vecOf_ne_zero hn₀).symm
    rw [if_pos h0, if_neg hne, roughPart_eq_self h0]
    have hpos : 0 ≤ (Real.sqrt n)⁻¹ := by positivity
    rw [abs_mul, abs_of_nonneg hpos]
    have : |(1 + ε ^ 2) * 1 + ε * 0| ≤ 3 * Real.sqrt n₀ := by
      rw [mul_one, mul_zero, add_zero, abs_of_nonneg (by positivity)]
      nlinarith
    exact mul_le_mul_of_nonneg_right this hpos
  · rw [if_neg h0]
    by_cases h1 : vecOf P n = vecOf P n₀
    · rw [if_pos h1]
      have hnr := eq_mul_roughPart (P := P) hn hn₀ h1
      have hr0 : (0 : ℝ) < roughPart P n := by exact_mod_cast roughPart_pos hn
      have hsq : (Real.sqrt (roughPart P n))⁻¹ = Real.sqrt n₀ * (Real.sqrt n)⁻¹ := by
        have e : (n : ℝ) = n₀ * roughPart P n := by exact_mod_cast hnr
        rw [e, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv, ← mul_assoc,
          mul_inv_cancel₀ (by positivity : Real.sqrt n₀ ≠ 0), one_mul]
      rw [hsq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt n₀ * (Real.sqrt n)⁻¹)]
      have : |(1 + ε ^ 2) * 0 + ε * 1| ≤ 3 := by
        rw [mul_zero, zero_add, mul_one]
        linarith
      exact (mul_le_mul_of_nonneg_right this (by positivity)).trans (le_of_eq (by ring))
    · rw [if_neg h1]
      simp only [mul_zero, add_zero, zero_mul, abs_zero]
      positivity

theorem abs_tsum_le_tsum_abs {g : ℕ → ℝ} (h : Summable fun n => |g n|) :
    |∑' n, g n| ≤ ∑' n, |g n| := by
  have hg : Summable g := h.of_abs
  rw [abs_le]
  constructor
  · rw [← tsum_neg]
    exact h.neg.tsum_le_tsum (fun n => neg_abs_le _) hg
  · exact hg.tsum_le_tsum (fun n => le_abs_self _) h

theorem rankinConst_nonneg (J : ℕ) : 0 ≤ rankinConst J := by
  unfold rankinConst
  positivity

/-- The remainder of the weighted moment at a general twist, against `mainWeight`. -/
theorem exists_norm_weightedMoment_sub_mainWeight_le (hP : ∀ p ∈ P, p.Prime) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L δ : ℝ}, 16 ≤ L → 0 < δ → δ ≤ 1 / 4 → ∀ (ε : ℝ) {n n₀ : ℕ},
      n ≠ 0 → IsSmoothOver P n₀ →
      ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
          ((mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2) : ℝ) : ℂ) * logWindow L‖ ≤
        (∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes), |modeCoeff ε j c|) *
          (2 * L * Real.sqrt (twistBound P n₀) * (C + 2 * Real.log (twistBound P n₀) + 2) *
              ((1 + Real.log n) * (Real.sqrt n)⁻¹) +
            C * (24 * δ * (twistBound P n₀ : ℝ) * L * Real.sqrt L + L ^ 2 / (L * δ) ^ K +
              L ^ 2 * Real.exp (-(L ^ 2) / 32))) := by
  obtain ⟨C, hC, hmain⟩ := exists_norm_weightedMoment_sub_main_le_general hP K
  refine ⟨C, hC, fun {L δ} hL hδ hδ4 ε {n n₀} hn hn₀ => ?_⟩
  have hL0 : 0 < L := by linarith
  have h := hmain hL hδ hδ4 ε hn hn₀
  have hEeq : ((mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2) : ℝ) : ℂ) =
      ((((1 + ε ^ 2) * (if vecOf P n = 0 then 1 else 0) +
        ε * (if vecOf P n = vecOf P n₀ then 1 else 0)) * ∏ p : P, (1 - primeHalf p ^ 2)) *
          (Real.sqrt (roughPart P n))⁻¹ : ℝ) := by
    unfold mainWeight
    congr 1
    ring
  rw [hEeq]
  refine h.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun c hc => ?_
  exact mul_le_mul_of_nonneg_left (hkEnvelope_mode_le hP hC hL0 hδ K hn hj hc) (abs_nonneg _)

/-! ## Rankin bookkeeping -/

theorem exists_finset_log_le (M : ℝ) : ∃ F : Finset ℕ, ∀ n, n ∈ F ↔ Real.log n ≤ M := by
  classical
  refine ⟨(Finset.range (⌊Real.exp M⌋₊ + 1)).filter (fun n => Real.log n ≤ M), fun n => ?_⟩
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · omega
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    have : (n : ℝ) ≤ Real.exp M := by
      rw [← Real.exp_log hn0']
      exact Real.exp_le_exp.mpr h
    have := Nat.le_floor this
    omega

/-- Finite remainder sums against the Rankin weights. -/
theorem sum_abs_mul_le_of_pointwise {v : ℕ → ℝ} {J : ℕ}
    (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) ^ J)⁻¹)
    (hsR : Summable fun n : ℕ => |v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹)
    {F : Finset ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hF : ∀ n ∈ F, Real.log n ≤ M) {e : ℕ → ℝ}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : ∀ n, |v n| * e n ≤ a * (|v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹) + b * |v n|) :
    ∑ n ∈ F, |v n| * e n ≤ a * ∑' n : ℕ, |v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹ +
      b * ((1 + M) ^ J * ∑' n : ℕ, |v n| * ((1 + Real.log n) ^ J)⁻¹) := by
  have h1 := Finset.sum_le_sum fun n (_ : n ∈ F) => he n
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
  have h2 : ∑ n ∈ F, |v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹ ≤
      ∑' n : ℕ, |v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹ :=
    hsR.sum_le_tsum F fun n _ => mul_nonneg (mul_nonneg (abs_nonneg _) (one_add_log_nonneg n))
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have h3 := sum_abs_le_of_log_le hs hM0 hF
  exact h1.trans (add_le_add (mul_le_mul_of_nonneg_left h2 ha) (mul_le_mul_of_nonneg_left h3 hb))

/-- Tails beyond `log n > M` against the Rankin weights. -/
theorem abs_tsum_compl_le {v : ℕ → ℝ} {J : ℕ}
    (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) ^ J)⁻¹)
    {F : Finset ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hF : ∀ n, n ∉ F → M < Real.log n) {g : ℕ → ℝ}
    {K : ℕ} (hJK : J ≤ K) {c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ n, n ∉ F → |g n| ≤ c * (|v n| * ((1 + Real.log n) ^ K)⁻¹)) :
    |∑' n, (if n ∈ F then 0 else g n)| ≤
      c * (((1 + M) ^ (K - J))⁻¹ * ∑' n : ℕ, |v n| * ((1 + Real.log n) ^ J)⁻¹) := by
  obtain ⟨htS, htB⟩ := tsum_tail_le hs hJK hM0
  have hpt : ∀ n : ℕ, |if n ∈ F then 0 else g n| ≤
      c * (if Real.log n ≤ M then 0 else |v n| * ((1 + Real.log n) ^ K)⁻¹) := by
    intro n
    by_cases hnF : n ∈ F
    · rw [if_pos hnF, abs_zero]
      exact mul_nonneg hc (by split_ifs <;> positivity)
    · rw [if_neg hnF, if_neg (not_le.mpr (hF n hnF))]
      exact hg n hnF
  have hhs : Summable (fun n => |if n ∈ F then 0 else g n|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpt (htS.mul_left c)
  calc |∑' n, (if n ∈ F then 0 else g n)| ≤ ∑' n : ℕ, |if n ∈ F then 0 else g n| :=
        abs_tsum_le_tsum_abs hhs
    _ ≤ ∑' n : ℕ, c * (if Real.log n ≤ M then 0 else |v n| * ((1 + Real.log n) ^ K)⁻¹) :=
        hhs.tsum_le_tsum hpt (htS.mul_left c)
    _ = c * ∑' n : ℕ, (if Real.log n ≤ M then 0 else |v n| * ((1 + Real.log n) ^ K)⁻¹) :=
        tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left htB hc

/-- `(log L + 2) e^{−M/4} ≤ 32J + 2` at `L = M^{8J}`. -/
theorem log_scale_mul_exp_le {J : ℕ} {M : ℝ} (hM : 2 ≤ M) :
    (Real.log (M ^ (8 * J)) + 2) * Real.exp (-(M / 4)) ≤ 32 * J + 2 := by
  have hlogL : Real.log (M ^ (8 * J)) ≤ 8 * J * M := by
    rw [Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < M by linarith)
    push_cast
    have hJ0 : (0 : ℝ) ≤ 8 * J := by positivity
    nlinarith
  have hMexp : M * Real.exp (-(M / 4)) ≤ 4 := by
    have := mul_exp_neg_le_one (M / 4)
    linarith
  have hexp1 : Real.exp (-(M / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpos := Real.exp_pos (-(M / 4))
  calc (Real.log (M ^ (8 * J)) + 2) * Real.exp (-(M / 4))
      ≤ (8 * J * M + 2) * Real.exp (-(M / 4)) := mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ = 8 * J * (M * Real.exp (-(M / 4))) + 2 * Real.exp (-(M / 4)) := by ring
    _ ≤ 8 * J * 4 + 2 * 1 := by
        have hJ0 : (0 : ℝ) ≤ 8 * J := by positivity
        nlinarith
    _ = 32 * J + 2 := by ring

/-- The main-weight series is summable. -/
theorem summable_mul_mainWeight {v : ℕ → ℝ} (hv0 : v 0 = 0)
    (hsR : Summable fun n : ℕ => |v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹) {ε : ℝ}
    (hε : |ε| ≤ 1) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀) :
    Summable fun n => v n * mainWeight P ε n₀ n := by
  refine Summable.of_norm_bounded (hsR.mul_left (3 * Real.sqrt n₀)) fun n => ?_
  rw [Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [hv0, zero_mul, abs_zero]
    positivity
  rw [abs_mul]
  have h1 := abs_mainWeight_le hε hn₀ (Nat.pos_iff_ne_zero.mp hn0)
  have hl : 1 ≤ 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
  calc |v n| * |mainWeight P ε n₀ n| ≤ |v n| * (3 * Real.sqrt n₀ * (Real.sqrt n)⁻¹) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ ≤ |v n| * (3 * Real.sqrt n₀ * ((1 + Real.log n) * (Real.sqrt n)⁻¹)) := by
        gcongr
        nlinarith [inv_nonneg.mpr (Real.sqrt_nonneg (n : ℝ))]
    _ = 3 * Real.sqrt n₀ * (|v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹) := by ring

/-- **The key inequality at a fixed truncation**: for `Y = Σ_n v(n) mainWeight(n)`,
`Y Π_p(1 − 1/p) L log L ≤ C L` at every scale `L = M^{8J}`. -/
theorem exists_key_bound_trunc (hP : ∀ p ∈ P, p.Prime) {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A) {J : ℕ} (hJ : 2 ≤ J)
    (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) ^ J)⁻¹)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℝ, 2 ≤ M →
      (∑' n : ℕ, v n * mainWeight P ε n₀ n) * (∏ p : P, (1 - primeHalf p ^ 2)) *
          (M ^ (8 * J) * Real.log (M ^ (8 * J))) ≤ C * M ^ (8 * J) := by
  have hεabs : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> simp
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑' n : ℕ, |v n| * ((1 + Real.log n) ^ J)⁻¹ := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]; exact tsum_nonneg fun n => by have := one_add_log_nonneg n; positivity
  obtain ⟨C_T, hC_T, hmain⟩ := exists_norm_weightedMoment_sub_mainWeight_le hP 5
  obtain ⟨C_M, hC_M, hdecay⟩ := exists_norm_weightedMoment_mul_pow_le P ε n₀ (25 * J)
  obtain ⟨hsR, hR⟩ := tsum_abs_mul_log_inv_sqrt_le hs
  rw [← hS] at hR
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = (twistBound P n₀ : ℝ) := ⟨_, rfl⟩
  have hK₀1 : 1 ≤ K₀ := by rw [hK₀]; exact_mod_cast twistBound_pos hP n₀
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
      |modeCoeff ε j c| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hB]; exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => abs_nonneg _
  obtain ⟨C₅, hC₅⟩ : ∃ C₅ : ℝ, C₅ = C_T + 2 * Real.log K₀ + 2 := ⟨_, rfl⟩
  have hC₅0 : 0 ≤ C₅ := by rw [hC₅]; have := Real.log_nonneg hK₀1; positivity
  obtain ⟨eP, heP⟩ : ∃ eP : ℝ, eP = ∏ p : P, (1 - primeHalf p ^ 2) := ⟨_, rfl⟩
  have heP0 : 0 < eP := by rw [heP]; exact eulerProduct_pos hP
  have heP1 : eP ≤ 1 := by
    rw [heP]
    refine Finset.prod_le_one (fun p _ => ?_) (fun p _ => ?_)
    · rw [primeHalf_sq]
      have h2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast (hP p p.2).two_le
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    · have := sq_nonneg (primeHalf p)
      linarith
  rw [← heP]
  obtain ⟨CJ, hCJ⟩ : ∃ CJ : ℝ, CJ = J.factorial * 4 ^ J * Real.exp (1 / 4) := ⟨_, rfl⟩
  have hCJ0 : 0 ≤ CJ := by rw [hCJ]; positivity
  have hrk := rankinConst_nonneg J
  have hsqn₀ : 0 ≤ Real.sqrt n₀ := Real.sqrt_nonneg _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = B * (2 * Real.sqrt K₀ * C₅ * (rankinConst J * S) +
      C_T * ((24 * K₀ + 33) * 2 ^ J) * S) + C_M * S +
      2 * (32 * J + 2) * (3 * Real.sqrt n₀ * CJ * S) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]
    have h1 : 0 ≤ 2 * Real.sqrt K₀ * C₅ * (rankinConst J * S) :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) hC₅0)
        (mul_nonneg hrk hS0)
    have h2 : 0 ≤ C_T * ((24 * K₀ + 33) * 2 ^ J) * S :=
      mul_nonneg (mul_nonneg hC_T (mul_nonneg (by linarith) (by positivity))) hS0
    have h3 : 0 ≤ 2 * (32 * (J : ℝ) + 2) * (3 * Real.sqrt n₀ * CJ * S) := by positivity
    exact add_nonneg (add_nonneg (mul_nonneg hB0 (add_nonneg h1 h2)) (mul_nonneg hC_M hS0)) h3
  refine ⟨C, hC0, fun M hM => ?_⟩
  obtain ⟨hL16, hδ0, hδ4, hE, hL3⟩ := scale_bounds hJ hM K₀ (by linarith)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = M ^ (8 * J) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (M ^ (6 * J))⁻¹ := ⟨_, rfl⟩
  rw [← hL] at hL16 hL3 hE ⊢
  rw [← hδ] at hδ0 hδ4 hE
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = ∑' n : ℕ, v n * mainWeight P ε n₀ n := ⟨_, rfl⟩
  rw [← hY]
  rcases le_or_gt Y 0 with hY0 | hYpos
  · have hLlog : 0 ≤ L * Real.log L := mul_nonneg hL0.le (Real.log_nonneg hL1)
    have : Y * eP * (L * Real.log L) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hY0 heP0.le) hLlog
    have := mul_nonneg hC0 hL0.le
    linarith
  -- the pairing inequality
  have hpair := sum_mul_re_weightedMoment_nonpos_of_summable hv0 hA ha hJ hs hPD hL0
    (notchWeight_nonneg P ε n₀) (contDiff_notchWeight P ε n₀ _)
  have hMdec : ∀ n : ℕ, ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n)‖ ≤
      C_M * L ^ 3 * ((1 + Real.log n) ^ (25 * J))⁻¹ := by
    intro n
    have h := hdecay hL16 (Real.log n)
    rw [abs_of_nonneg (Real.log_natCast_nonneg n)] at h
    have hpos : 0 < (1 + Real.log n) ^ (25 * J) := pow_pos (by
      linarith [Real.log_natCast_nonneg n]) _
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    exact h
  have hfg : ∀ n : ℕ, |v n * (ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n)).re| ≤
      C_M * L ^ 3 * (|v n| * ((1 + Real.log n) ^ (25 * J))⁻¹) := by
    intro n
    rw [abs_mul]
    calc |v n| * |(ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n)).re|
        ≤ |v n| * (C_M * L ^ 3 * ((1 + Real.log n) ^ (25 * J))⁻¹) :=
          mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hMdec n)) (abs_nonneg _)
      _ = _ := by ring
  have hfs : Summable fun n : ℕ =>
      v n * (ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n)).re := by
    refine Summable.of_norm_bounded (hs.mul_left (C_M * L ^ 3)) fun n => ?_
    rw [Real.norm_eq_abs]
    refine (hfg n).trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC_M (pow_nonneg hL0.le 3)))
    have h1 : 1 ≤ 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
      (pow_le_pow_right₀ h1 (by omega))) (abs_nonneg _)
  obtain ⟨F, hFmem⟩ := exists_finset_log_le M
  have hF' : ∀ n, n ∉ F → M < Real.log n := fun n hn => lt_of_not_ge fun h => hn ((hFmem n).mpr h)
  rw [split_tsum hfs F] at hpair
  have hmws := summable_mul_mainWeight (P := P) hv0 hsR hεabs hn₀
  have hsplitY := split_tsum hmws F
  rw [← hY] at hsplitY
  -- the decomposition on `F`
  have hfF : ∑ n ∈ F, v n * (ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n)).re =
      eP * (logWindow L).re * ∑ n ∈ F, v n * mainWeight P ε n₀ n +
        ∑ n ∈ F, v n * (ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
          ((mainWeight P ε n₀ n * eP : ℝ) : ℂ) * logWindow L).re := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.sub_re, Complex.re_ofReal_mul]
    ring
  -- the remainders on `F`
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 24 * δ * K₀ * L * Real.sqrt L + L ^ 2 / (L * δ) ^ 5 +
      L ^ 2 * Real.exp (-(L ^ 2) / 32) := ⟨_, rfl⟩
  have hU0 : 0 ≤ U := by
    rw [hU]
    have hK0 : 0 ≤ K₀ := by linarith
    have h1 : 0 ≤ 24 * δ * K₀ * L * Real.sqrt L :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hδ0.le) hK0) hL0.le)
        (Real.sqrt_nonneg _)
    have h2 : 0 ≤ L ^ 2 / (L * δ) ^ 5 :=
      div_nonneg (sq_nonneg _) (pow_nonneg (mul_nonneg hL0.le hδ0.le) _)
    have h3 : 0 ≤ L ^ 2 * Real.exp (-(L ^ 2) / 32) := mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    linarith
  have hEb : ∀ n : ℕ, |v n| * ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
      ((mainWeight P ε n₀ n * eP : ℝ) : ℂ) * logWindow L‖ ≤
      B * (2 * L * Real.sqrt K₀ * C₅) * (|v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹) +
        B * C_T * U * |v n| := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [hv0, abs_zero, zero_mul]
      simp
    have h := hmain hL16 hδ0 hδ4 ε (Nat.pos_iff_ne_zero.mp hn0) hn₀
    rw [← heP, ← hB, ← hK₀] at h
    rw [show C_T + 2 * Real.log K₀ + 2 = C₅ from hC₅.symm, ← hU] at h
    calc |v n| * ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
          ((mainWeight P ε n₀ n * eP : ℝ) : ℂ) * logWindow L‖
        ≤ |v n| * (B * (2 * L * Real.sqrt K₀ * C₅ * ((1 + Real.log n) * (Real.sqrt n)⁻¹) +
            C_T * U)) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = _ := by ring
  have hsumF := sum_abs_mul_le_of_pointwise hs hsR hM0 (fun n hn => (hFmem n).mp hn)
    (mul_nonneg hB0 (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hL0.le)
      (Real.sqrt_nonneg _)) hC₅0)) (mul_nonneg (mul_nonneg hB0 hC_T) hU0) hEb
  rw [← hS] at hsumF
  -- the crude tail
  have htailb := abs_tsum_compl_le hs hM0 hF' (K := 25 * J) (by omega)
    (mul_nonneg hC_M (pow_nonneg hL0.le 3)) (fun n _ => hfg n)
  rw [← hS, show 25 * J - J = 24 * J by omega] at htailb
  -- the main-term tail
  have hTmb := abs_tsum_compl_le hs hM0 hF' (g := fun n => v n * mainWeight P ε n₀ n) (K := J)
    le_rfl (c := 3 * Real.sqrt n₀ * (Real.exp (-(M / 4)) * CJ))
    (mul_nonneg (mul_nonneg (by norm_num) hsqn₀) (mul_nonneg (Real.exp_pos _).le hCJ0))
    (fun n hn => by
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · rw [hv0, zero_mul, abs_zero]
        simp
      have h1 := abs_mainWeight_le hεabs hn₀ (Nat.pos_iff_ne_zero.mp hn0)
      have h2 := inv_sqrt_le_of_log_gt J (hF' n hn)
      rw [← hCJ] at h2
      rw [abs_mul]
      calc |v n| * |mainWeight P ε n₀ n| ≤ |v n| * (3 * Real.sqrt n₀ * (Real.sqrt n)⁻¹) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ ≤ |v n| * (3 * Real.sqrt n₀ * (Real.exp (-(M / 4)) *
              (CJ * ((1 + Real.log n) ^ J)⁻¹))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2
              (mul_nonneg (by norm_num) hsqn₀)) (abs_nonneg _)
        _ = _ := by ring)
  rw [← hS, Nat.sub_self, pow_zero, inv_one, one_mul] at hTmb
  -- the window bounds
  have hlogWn := norm_logWindow_le (show (2 : ℝ) ≤ L by linarith)
  have hlogexp := log_scale_mul_exp_le (J := J) hM
  rw [← hL] at hlogexp
  have hlogWre := re_logWindow_ge (show 2 ≤ L by linarith)
  set Tm := ∑' n, (if n ∈ F then 0 else v n * mainWeight P ε n₀ n) with hTmdef
  have hTmW : ‖logWindow L‖ * |Tm| ≤ 2 * (32 * J + 2) * (3 * Real.sqrt n₀ * CJ * S) * L := by
    calc ‖logWindow L‖ * |Tm| ≤ (2 * L * (Real.log L + 2)) *
          (3 * Real.sqrt n₀ * (Real.exp (-(M / 4)) * CJ) * S) :=
          mul_le_mul hlogWn hTmb (abs_nonneg _)
            (mul_nonneg (mul_nonneg zero_le_two hL0.le) (by linarith [Real.log_nonneg hL1]))
      _ = 2 * L * (3 * Real.sqrt n₀ * CJ * S) * ((Real.log L + 2) * Real.exp (-(M / 4))) := by
          ring
      _ ≤ 2 * L * (3 * Real.sqrt n₀ * CJ * S) * (32 * J + 2) :=
          mul_le_mul_of_nonneg_left hlogexp (mul_nonneg (mul_nonneg zero_le_two hL0.le)
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsqn₀) hCJ0) hS0))
      _ = 2 * (32 * J + 2) * (3 * Real.sqrt n₀ * CJ * S) * L := by ring
  have hTmle : eP * (logWindow L).re * Tm ≤ ‖logWindow L‖ * |Tm| := by
    have hre0 : 0 ≤ (logWindow L).re :=
      le_trans (mul_nonneg hL0.le (Real.log_nonneg hL1)) hlogWre
    calc eP * (logWindow L).re * Tm ≤ eP * (logWindow L).re * |Tm| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg heP0.le hre0)
      _ ≤ 1 * ‖logWindow L‖ * |Tm| :=
          mul_le_mul_of_nonneg_right (mul_le_mul heP1 (Complex.re_le_norm _) hre0 zero_le_one)
            (abs_nonneg _)
      _ = ‖logWindow L‖ * |Tm| := by ring
  have hmainpos : Y * eP * (L * Real.log L) ≤ Y * eP * (logWindow L).re :=
    mul_le_mul_of_nonneg_left hlogWre (mul_nonneg hYpos.le heP0.le)
  have hFabs : |∑ n ∈ F, v n * (ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
      ((mainWeight P ε n₀ n * eP : ℝ) : ℂ) * logWindow L).re| ≤
      ∑ n ∈ F, |v n| * ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n) -
        ((mainWeight P ε n₀ n * eP : ℝ) : ℂ) * logWindow L‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
  rw [hfF] at hpair
  have hYsplit : ∑ n ∈ F, v n * mainWeight P ε n₀ n = Y - Tm := by
    rw [hsplitY]
    ring
  rw [hYsplit] at hpair
  have h1 := neg_abs_le (∑ n ∈ F, v n * (ZetaNotch.weightedMoment L (notchWeight P ε n₀)
    (Real.log n) - ((mainWeight P ε n₀ n * eP : ℝ) : ℂ) * logWindow L).re)
  have h2 := neg_abs_le (∑' n, (if n ∈ F then 0 else
    v n * (ZetaNotch.weightedMoment L (notchWeight P ε n₀) (Real.log n)).re))
  have hR' : B * (2 * L * Real.sqrt K₀ * C₅) *
      ∑' n : ℕ, |v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹ ≤
      B * (2 * L * Real.sqrt K₀ * C₅) * (rankinConst J * S) :=
    mul_le_mul_of_nonneg_left hR (mul_nonneg hB0 (mul_nonneg (mul_nonneg
      (mul_nonneg zero_le_two hL0.le) (Real.sqrt_nonneg _)) hC₅0))
  have hEU : B * C_T * U * ((1 + M) ^ J * S) ≤ B * C_T * S * ((24 * K₀ + 33) * 2 ^ J * L) := by
    have hE' : (1 + M) ^ J * U ≤ (24 * K₀ + 33) * 2 ^ J * L := by rw [hU]; exact hE
    calc B * C_T * U * ((1 + M) ^ J * S) = B * C_T * S * ((1 + M) ^ J * U) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hE' (mul_nonneg (mul_nonneg hB0 hC_T) hS0)
  have htail' : C_M * L ^ 3 * (((1 + M) ^ (24 * J))⁻¹ * S) ≤ C_M * S * L := by
    calc C_M * L ^ 3 * (((1 + M) ^ (24 * J))⁻¹ * S) = C_M * S * (L ^ 3 * ((1 + M) ^ (24 * J))⁻¹) :=
          by ring
      _ ≤ C_M * S * 1 := mul_le_mul_of_nonneg_left hL3 (mul_nonneg hC_M hS0)
      _ ≤ C_M * S * L := mul_le_mul_of_nonneg_left hL1 (mul_nonneg hC_M hS0)
  rw [hC]
  linarith [hsumF, htailb, hFabs, hmainpos, hpair, hTmW, hTmle, hR', hEU, htail', h1, h2]

/-- A positive `Y` is incompatible with `Y e L log L ≤ C L` at all scales `L = M^{8J}`. -/
theorem nonpos_of_scale_bound {Y e C : ℝ} {J : ℕ} (hJ : 1 ≤ J) (he : 0 < e)
    (h : ∀ M : ℝ, 2 ≤ M → Y * e * (M ^ (8 * J) * Real.log (M ^ (8 * J))) ≤ C * M ^ (8 * J)) :
    Y ≤ 0 := by
  by_contra hY
  push Not at hY
  set a : ℝ := Y * e with ha
  have ha0 : 0 < a := mul_pos hY he
  have hJ0 : (0 : ℝ) < 8 * J := by
    have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  set M : ℝ := max 2 (Real.exp (|C| / (a * (8 * J)) + 1)) with hM
  have hM2 : 2 ≤ M := le_max_left _ _
  have hMe : Real.exp (|C| / (a * (8 * J)) + 1) ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  have hlogM : |C| / (a * (8 * J)) + 1 ≤ Real.log M := by
    rw [← Real.log_exp (|C| / (a * (8 * J)) + 1)]
    exact Real.log_le_log (Real.exp_pos _) hMe
  have hkey := h M hM2
  have hL0 : 0 < M ^ (8 * J) := by positivity
  have hlogL : Real.log (M ^ (8 * J)) = 8 * J * Real.log M := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlogL] at hkey
  have h1 : a * (8 * J * Real.log M) ≤ C := by
    have : a * (8 * J * Real.log M) * M ^ (8 * J) ≤ C * M ^ (8 * J) := by
      calc a * (8 * J * Real.log M) * M ^ (8 * J) =
            Y * e * (M ^ (8 * J) * (8 * J * Real.log M)) := by rw [ha]; ring
        _ ≤ C * M ^ (8 * J) := hkey
    exact le_of_mul_le_mul_right this hL0
  have h2 : |C| < a * (8 * J * Real.log M) := by
    have hpos : 0 < a * (8 * J) := mul_pos ha0 hJ0
    have : |C| / (a * (8 * J)) < Real.log M := by linarith
    rw [div_lt_iff₀ hpos] at this
    linarith
  linarith [le_abs_self C]

/-- The tail `Σ_{n > y} |v(n)| n^{−1/2}`. -/
def roughTail (v : ℕ → ℝ) (y : ℕ) : ℝ :=
  ∑' n : ℕ, if y < n then |v n| * (Real.sqrt n)⁻¹ else 0

theorem tendsto_roughTail {v : ℕ → ℝ} (hsum : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹) :
    Tendsto (roughTail v) atTop (𝓝 0) := by
  have e : ∀ y : ℕ, roughTail v y =
      ∑' k : ℕ, |v (k + (y + 1))| * (Real.sqrt ((k + (y + 1) : ℕ) : ℝ))⁻¹ := by
    intro y
    unfold roughTail
    have hs' : Summable (fun n : ℕ => if y < n then |v n| * (Real.sqrt n)⁻¹ else 0) := by
      refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_) hsum
      split_ifs
      · exact le_refl _
      · positivity
    rw [← hs'.sum_add_tsum_nat_add (y + 1)]
    have h0 : ∑ i ∈ Finset.range (y + 1), (if y < i then |v i| * (Real.sqrt i)⁻¹ else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => if_neg (by rw [Finset.mem_range] at hi; omega)
    rw [h0, zero_add]
    refine tsum_congr fun k => ?_
    rw [if_pos (by omega)]
  have hlim := (tendsto_sum_nat_add (fun n : ℕ => |v n| * (Real.sqrt n)⁻¹)).comp
    (tendsto_add_atTop_nat 1)
  refine hlim.congr fun y => ?_
  simp only [Function.comp_apply]
  rw [e]

theorem isSmoothOver_primesUpTo {y n₀ : ℕ} (hn₀2 : 2 ≤ n₀) (hy : n₀ ≤ y) :
    IsSmoothOver (primesUpTo y) n₀ :=
  ⟨hn₀2, fun _ hp => mem_primesUpTo.mpr
    ⟨(Nat.le_of_mem_primeFactors hp).trans hy, Nat.prime_of_mem_primeFactors hp⟩⟩

/-- **The fibre limit.** If `Σ_n |v(n)| n^{−1/2} < ∞` and, for every truncation `P_y` with
`n₀ ≤ y` and both signs `ε = ±1`, the main-term functional `Σ_n v(n) mainWeight(n)` is `≤ 0`,
then `v = 0`: the two fibres of the functional isolate `v(n₀)` up to `(2 + √n₀) Σ_{n>y}|v(n)|n^{−1/2}`. -/
theorem eq_zero_of_forall_mainWeight_nonpos {v : ℕ → ℝ} (hv0 : v 0 = 0) (hv1 : v 1 = 0)
    (hsq : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹)
    (hY : ∀ y n₀ : ℕ, 2 ≤ n₀ → n₀ ≤ y → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ∑' n, v n * mainWeight (primesUpTo y) ε n₀ n ≤ 0) :
    v = 0 := by
  funext n₀
  by_contra hne
  have hn₀2 : 2 ≤ n₀ := by
    rcases n₀ with _ | _ | n
    · exact absurd hv0 hne
    · exact absurd hv1 hne
    · omega
  have hbound : ∀ y : ℕ, n₀ ≤ y → |v n₀| ≤ (2 + Real.sqrt n₀) * roughTail v y := by
    intro y hy
    set P := primesUpTo y with hPdef
    have hP : ∀ p ∈ P, p.Prime := prime_of_mem_primesUpTo
    have hn₀s : IsSmoothOver P n₀ := isSmoothOver_primesUpTo hn₀2 hy
    have hYneg : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∑' n, v n * mainWeight P ε n₀ n ≤ 0 :=
      hY y n₀ hn₀2 hy
    -- the two fibres
    have hsq₀ : 1 ≤ Real.sqrt n₀ := Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ n₀))
    set g₀ : ℕ → ℝ := fun n => if vecOf P n = 0 then v n * (Real.sqrt (roughPart P n))⁻¹ else 0
      with hg₀
    set g₁ : ℕ → ℝ := fun n => if vecOf P n = vecOf P n₀ then
      v n * (Real.sqrt (roughPart P n))⁻¹ else 0 with hg₁
    have hg₀b : ∀ n, |g₀ n| ≤ if y < n then |v n| * (Real.sqrt n)⁻¹ else 0 := by
      intro n
      simp only [hg₀]
      by_cases h0 : vecOf P n = 0
      · rw [if_pos h0, roughPart_eq_self h0, abs_mul,
          abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (n : ℝ)))]
        by_cases hyn : y < n
        · rw [if_pos hyn]
        · rw [if_neg hyn]
          have hn2 : ¬ 2 ≤ n := fun h2 => hyn (lt_of_vecOf_eq_zero h2 h0)
          have : v n = 0 := by
            rcases n with _ | _ | n
            · exact hv0
            · exact hv1
            · omega
          rw [this, abs_zero, zero_mul]
      · rw [if_neg h0, abs_zero]
        split_ifs <;> positivity
    have hfib : ∀ n, vecOf P n = vecOf P n₀ →
        (Real.sqrt (roughPart P n))⁻¹ = Real.sqrt n₀ * (Real.sqrt n)⁻¹ ∧ (n ≠ n₀ → y < n) := by
      intro n h1
      have hn : n ≠ 0 := by
        rintro rfl
        apply vecOf_ne_zero hn₀s
        rw [← h1]
        funext p
        simp [vecOf]
      have hnr := eq_mul_roughPart (P := P) hn hn₀s h1
      constructor
      · have e : (n : ℝ) = n₀ * roughPart P n := by exact_mod_cast hnr
        rw [e, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv, ← mul_assoc,
          mul_inv_cancel₀ (by positivity : Real.sqrt n₀ ≠ 0), one_mul]
      · intro hnn
        have hr1 : roughPart P n ≠ 1 := fun hr => hnn (by rw [hnr, hr, mul_one])
        have hr0 := roughPart_pos (P := P) hn
        have hy := lt_of_vecOf_eq_zero (y := y) (n := roughPart P n) (by omega)
          (vecOf_roughPart hP hn)
        have : roughPart P n ≤ n :=
          calc roughPart P n ≤ n₀ * roughPart P n := Nat.le_mul_of_pos_left _ (by omega)
            _ = n := hnr.symm
        omega
    have hg₁b : ∀ n, |g₁ n| ≤ Real.sqrt n₀ * (|v n| * (Real.sqrt n)⁻¹) := by
      intro n
      simp only [hg₁]
      by_cases h1 : vecOf P n = vecOf P n₀
      · rw [if_pos h1, (hfib n h1).1, abs_mul,
          abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _)))]
        exact le_of_eq (by ring)
      · rw [if_neg h1, abs_zero]
        positivity
    have hg₁t : ∀ n, |if n = n₀ then 0 else g₁ n| ≤
        Real.sqrt n₀ * (if y < n then |v n| * (Real.sqrt n)⁻¹ else 0) := by
      intro n
      by_cases hnn : n = n₀
      · rw [if_pos hnn, abs_zero]
        split_ifs <;> positivity
      · rw [if_neg hnn]
        simp only [hg₁]
        by_cases h1 : vecOf P n = vecOf P n₀
        · rw [if_pos h1, (hfib n h1).1, if_pos ((hfib n h1).2 hnn), abs_mul,
            abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _)))]
          exact le_of_eq (by ring)
        · rw [if_neg h1, abs_zero]
          split_ifs <;> positivity
    have htail_s : Summable (fun n : ℕ => if y < n then |v n| * (Real.sqrt n)⁻¹ else 0) := by
      refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_) hsq
      split_ifs
      · exact le_refl _
      · positivity
    have hg₀s : Summable g₀ := Summable.of_norm_bounded htail_s fun n => by
      rw [Real.norm_eq_abs]; exact hg₀b n
    have hg₁s : Summable g₁ := Summable.of_norm_bounded (hsq.mul_left _) fun n => by
      rw [Real.norm_eq_abs]; exact hg₁b n
    have hdecomp : ∀ ε : ℝ, ∑' n, v n * mainWeight P ε n₀ n =
        (1 + ε ^ 2) * ∑' n, g₀ n + ε * ∑' n, g₁ n := by
      intro ε
      rw [← tsum_mul_left, ← tsum_mul_left, ← (hg₀s.mul_left _).tsum_add (hg₁s.mul_left _)]
      refine tsum_congr fun n => ?_
      simp only [hg₀, hg₁, mainWeight]
      split_ifs <;> ring
    have hB : |∑' n, g₀ n| ≤ roughTail v y :=
      (abs_tsum_le_tsum_abs (Summable.of_norm_bounded htail_s fun n => by
        rw [Real.norm_eq_abs, abs_abs]; exact hg₀b n)).trans
        (Summable.tsum_le_tsum hg₀b (Summable.of_norm_bounded htail_s fun n => by
          rw [Real.norm_eq_abs, abs_abs]; exact hg₀b n) htail_s)
    have hr₀ : roughPart P n₀ = 1 := by
      unfold roughPart
      rw [smoothPart_of_smooth hn₀s, Nat.div_self (by omega)]
    have hsplit₁ := hg₁s.tsum_eq_add_tsum_ite n₀
    have hg₁n₀ : g₁ n₀ = v n₀ := by
      simp only [hg₁, if_pos rfl, hr₀, Nat.cast_one, Real.sqrt_one, inv_one, mul_one]
    rw [hg₁n₀] at hsplit₁
    have hRs : Summable fun n => |if n = n₀ then 0 else g₁ n| :=
      Summable.of_nonneg_of_le (fun n => abs_nonneg _) hg₁t (htail_s.mul_left _)
    have hR : |∑' n, (if n = n₀ then 0 else g₁ n)| ≤ Real.sqrt n₀ * roughTail v y := by
      refine (abs_tsum_le_tsum_abs hRs).trans ?_
      rw [roughTail, ← tsum_mul_left]
      exact hRs.tsum_le_tsum hg₁t (htail_s.mul_left _)
    have hY1 := hYneg 1 (Or.inl rfl)
    have hY2 := hYneg (-1) (Or.inr rfl)
    rw [hdecomp] at hY1 hY2
    norm_num at hY1 hY2
    rw [hsplit₁] at hY1 hY2
    have ha1 := abs_le.mp hB
    have ha2 := abs_le.mp hR
    have hrt : 0 ≤ roughTail v y := tsum_nonneg fun n => by split_ifs <;> positivity
    rw [abs_le]
    constructor <;> nlinarith
  have hlim : Tendsto (fun y => (2 + Real.sqrt n₀) * roughTail v y) atTop (𝓝 0) := by
    have := (tendsto_roughTail hsq).const_mul (2 + Real.sqrt n₀)
    rwa [mul_zero] at this
  have hle : |v n₀| ≤ 0 := ge_of_tendsto hlim (eventually_atTop.mpr ⟨n₀, hbound⟩)
  exact hne (abs_nonpos_iff.mp hle)

/-- **Weil-cone rigidity for log-summable deviations.** If `v(0) = v(1) = 0`,
`|v(n)| ≤ 2 log n + A`, `Σ_n |v(n)|(1 + log n)^{−J} < ∞` and `−ψ_v` is positive definite, then
`v = 0`. -/
theorem eq_zero_of_positiveDefinite_neg_nullPotential_of_logSummable {v : ℕ → ℝ} (hv0 : v 0 = 0)
    (hv1 : v 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A) {J : ℕ}
    (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) ^ J)⁻¹)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) :
    v = 0 := by
  have hs2 : Summable fun n : ℕ => |v n| * ((1 + Real.log n) ^ (J + 2))⁻¹ := by
    refine Summable.of_nonneg_of_le (fun n => by have := one_add_log_nonneg n; positivity)
      (fun n => ?_) hs
    have h1 : 1 ≤ 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
      (pow_le_pow_right₀ h1 (by omega))) (abs_nonneg _)
  obtain ⟨hsR, -⟩ := tsum_abs_mul_log_inv_sqrt_le hs2
  have hsq : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹ := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsR
    have h1 : 1 ≤ 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
    have : 0 ≤ |v n| * (Real.sqrt n)⁻¹ := by positivity
    nlinarith
  refine eq_zero_of_forall_mainWeight_nonpos hv0 hv1 hsq fun y n₀ hn₀2 hy ε hε => ?_
  have hP : ∀ p ∈ primesUpTo y, p.Prime := prime_of_mem_primesUpTo
  obtain ⟨C, -, hC⟩ := exists_key_bound_trunc hP hv0 hA ha (J := J + 2) (by omega) hs2 hPD
    (isSmoothOver_primesUpTo hn₀2 hy) hε
  exact nonpos_of_scale_bound (by omega) (eulerProduct_pos hP) hC

/-- The same with `+ψ_v` positive definite. -/
theorem eq_zero_of_positiveDefinite_nullPotential_of_logSummable {v : ℕ → ℝ} (hv0 : v 0 = 0)
    (hv1 : v 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A) {J : ℕ}
    (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) ^ J)⁻¹)
    (hPD : PositiveDefiniteOnReal fun y => ((RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) :
    v = 0 := by
  have hneg := eq_zero_of_positiveDefinite_neg_nullPotential_of_logSummable (v := fun n => -v n)
    (by simp [hv0]) (by simp [hv1]) hA (fun n => by rw [abs_neg]; exact ha n)
    (by simpa only [abs_neg] using hs)
    (by simpa only [RHTower.WeilRegular.nullPotential_neg, neg_neg] using hPD)
  funext n
  have := congrFun hneg n
  simpa using this

/-- **Corollary.** A full-cone Weil-positive `lam` whose normalized deviation is log-summable,
`Σ_n |lam(n) − Λ(n)| n^{−1/2}(1 + log n)^{−J} < ∞`, equals `Λ` on all `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_logSummable {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam) {J : ℕ}
    (hs : Summable fun n : ℕ => |RHTower.WeilExcess.weilDeviation lam n| *
      ((1 + Real.log n) ^ J)⁻¹) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  set v := RHTower.WeilExcess.weilDeviation lam with hv
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_abs_weilDeviation_le hW
  have hv0 : v 0 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hv1 : v 1 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ) :=
    RHTower.WeilExcess.positiveDefiniteOnReal_neg_deviationPotential hW
  have h0 := eq_zero_of_positiveDefinite_neg_nullPotential_of_logSummable hv0 hv1 hC0 hC hs hPD
  intro n hn
  have h := congrFun h0 n
  rw [hv, RHTower.WeilExcess.weilDeviation, if_pos hn, Pi.zero_apply] at h
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · exact absurd h hsq.ne'

/-- **Corollary (sparse supports).** If `Σ_{n ∈ S} (1 + log n)^{−K} < ∞` (e.g.
`#(S ∩ [1, X]) ≪ (log X)^D` with `K > D + 1`), then every full-cone Weil-positive `lam` equal to `Λ`
off `S` equals `Λ`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_sparse {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam) {S : ℕ → Prop} [DecidablePred S] {K : ℕ}
    (hS : Summable fun n : ℕ => if S n then ((1 + Real.log n) ^ K)⁻¹ else 0)
    (hoff : ∀ n, 2 ≤ n → ¬ S n → lam n = ArithmeticFunction.vonMangoldt n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_abs_weilDeviation_le hW
  refine eq_vonMangoldt_of_weilPositiveFull_of_logSummable hW (J := K + 1) ?_
  refine Summable.of_nonneg_of_le (fun n => by have := one_add_log_nonneg n; positivity)
    (fun n => ?_) (hS.mul_left (2 + C))
  by_cases hSn : S n
  · rw [if_pos hSn]
    have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hpos : 0 < (1 + Real.log n) ^ K := by positivity
    have hv : |RHTower.WeilExcess.weilDeviation lam n| ≤ (2 + C) * (1 + Real.log n) := by
      nlinarith [hC n]
    calc |RHTower.WeilExcess.weilDeviation lam n| * ((1 + Real.log n) ^ (K + 1))⁻¹
        ≤ (2 + C) * (1 + Real.log n) * ((1 + Real.log n) ^ (K + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right hv (by positivity)
      _ = (2 + C) * ((1 + Real.log n) ^ K)⁻¹ := by
          rw [pow_succ]
          field_simp
  · rw [if_neg hSn, mul_zero]
    have hz : RHTower.WeilExcess.weilDeviation lam n = 0 := by
      unfold RHTower.WeilExcess.weilDeviation
      split_ifs with h2
      · rw [hoff n h2 hSn, sub_self, zero_div]
      · rfl
    rw [hz, abs_zero, zero_mul]

end RHTower.WeilLogSummable
