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

theorem abs_mainWeight_le (hP : ∀ p ∈ P, p.Prime) {ε : ℝ} (hε : |ε| ≤ 1) {n₀ n : ℕ}
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
    calc |(1 + ε ^ 2) * 1 + ε * 0| * (Real.sqrt n)⁻¹ ≤ 3 * Real.sqrt n₀ * (Real.sqrt n)⁻¹ :=
          mul_le_mul_of_nonneg_right this hpos
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
      calc |(1 + ε ^ 2) * 0 + ε * 1| * (Real.sqrt n₀ * (Real.sqrt n)⁻¹)
          ≤ 3 * (Real.sqrt n₀ * (Real.sqrt n)⁻¹) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = 3 * Real.sqrt n₀ * (Real.sqrt n)⁻¹ := by ring
    · rw [if_neg h1]
      simp only [mul_zero, add_zero, zero_mul, abs_zero]
      positivity

end RHTower.WeilLogSummable
