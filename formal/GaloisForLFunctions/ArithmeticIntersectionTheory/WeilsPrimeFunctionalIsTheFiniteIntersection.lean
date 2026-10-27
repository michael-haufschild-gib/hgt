import GaloisForLFunctions.ArithmeticIntersectionTheory.TheLocalFormsDoNotSum
import GaloisForLFunctions.RHTower.SeparatedBumpWeilPositivity
import GaloisForLFunctions.BiScaleUncertainty.WeilLagPacketCancellationAndPositivity

/-!
# Weil's prime functional is the finite intersection

This is the transition map from the characteristic circle to the scaling surface. A **log-atom
test** places a narrow real bump `φ` (support `[−δ/2, δ/2]`) at each point `log n` of a set of orders
`S ⊆ [1, M]`: `f(u) = Σ_{n ∈ S} x_n φ(u − log n)` (`logAtomTest`). Its autocorrelation at a lag `y`
collects the pairs `(m, n)` with `|y − log(m/n)| ≤ δ` (`logAtomAutocorr_eq`). If `δ < log(1 + 1/M)`, the
lags `log k`, `k ∈ ℕ`, see only exact ratios `k = m/n` (`eq_of_abs_log_sub_lt`), and

    Σ_k Λ(k) k^{−1/2} (f ⋆ f̃(log k) + f ⋆ f̃(−log k)) = ‖φ‖² Σ_{m,n ∈ S} x_m x_n P(m, n)
                                                    = ‖φ‖² Σ_p Q_p(x)            (`primeSum_logAtom_eq`).

Weil's prime functional on log-atom tests *is* the finite intersection pairing of the torsion orbits,
hence the sum of the transverse tower forms. In Weil's explicit formula
`W(f ⋆ f̃) = (archimedean + polar part) − prime part` (`literatureRHS_eq_archPolar_sub_prime`), so
**under RH the archimedean place and the pole pay for the sum of the local tower forms**
(`riemannHypothesis_archPolar_ge_towers`): for every log-atom cycle,

    ‖φ‖² Σ_p Q_p(x) ≤ Re (archimedean + polar part of W at f ⋆ f̃).

The local forms are bounded, their sum is not (`TheLocalFormsDoNotSum`); the archimedean self-energy
of an atom of width `δ` grows like `log(1/δ)` (`RHTower.SeparatedBump.levy_ge`). This is the Hodge
index in tower form: the sign of the global pairing is the comparison of the archimedean self-energy
with the sum of the prime towers.
-/

noncomputable section

open MeasureTheory Finset Complex
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory
open BiScaleUncertainty.ChebyshevGauge
  (literatureRHS_weilTest_eq_criticalWeilEnergy_of_riemannHypothesis)

variable {φ : ℝ → ℝ} {δ : ℝ}

/-- The **log-atom test** `f(u) = Σ_{n ∈ S} x_n φ(u − log n)`. -/
def logAtomTest (φ : ℝ → ℝ) (S : Finset ℕ) (x : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑ n ∈ S, x n * φ (u - Real.log n)

/-- The autocorrelation `(f ⋆ f̃)(y) = ∫ f(u) f(u − y) du` of a log-atom test. -/
def logAtomAutocorr (φ : ℝ → ℝ) (S : Finset ℕ) (x : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∫ u, logAtomTest φ S x u * logAtomTest φ S x (u - y)

theorem logAtomAutocorr_eq (hφ : ContDiff ℝ 2 φ) (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    (S : Finset ℕ) (x : ℕ → ℝ) (y : ℝ) :
    logAtomAutocorr φ S x y = ∑ m ∈ S, ∑ n ∈ S, x m * x n *
      ∫ u, φ (u - Real.log m) * φ (u - (y + Real.log n)) := by
  have e : ∀ u, logAtomTest φ S x u * logAtomTest φ S x (u - y) =
      ∑ m ∈ S, ∑ n ∈ S, x m * x n * (φ (u - Real.log m) * φ (u - (y + Real.log n))) := fun u => by
    unfold logAtomTest
    rw [sum_mul_sum]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    rw [show u - y - Real.log n = u - (y + Real.log n) by ring]
    ring
  unfold logAtomAutocorr
  simp_rw [e]
  rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ =>
    (RHTower.SeparatedBump.integrable_translate_mul_translate hφ hφs _ _).const_mul _]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun n _ =>
    (RHTower.SeparatedBump.integrable_translate_mul_translate hφ hφs _ _).const_mul _]
  exact sum_congr rfl fun n _ => integral_const_mul _ _

/-! ### Separation of the log-lattice -/

/-- **Lags see only exact ratios.** For orders `m, n ≤ M` and `k ≥ 1`, if
`|log k − (log m − log n)| < log(1 + 1/M)` then `k n = m`. -/
theorem eq_of_abs_log_sub_lt {k m n M : ℕ} (hk : 0 < k) (hm : 0 < m) (hn : 0 < n) (hmM : m ≤ M)
    (h : |Real.log k - (Real.log m - Real.log n)| < Real.log (1 + 1 / M)) : k * n = m := by
  by_contra hne
  have hM : (0 : ℝ) < M := by exact_mod_cast (hm.trans_le hmM)
  have hkn : (0 : ℝ) < (k * n : ℕ) := by exact_mod_cast Nat.mul_pos hk hn
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log k - (Real.log m - Real.log n) = Real.log ((k * n : ℕ) : ℝ) - Real.log m := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hk.ne') (by exact_mod_cast hn.ne')]; ring
  rw [hlog] at h
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- `kn ≤ m − 1`: then `m/(kn) ≥ 1 + 1/M`
    have h1 : ((k * n : ℕ) : ℝ) * (1 + 1 / M) ≤ m := by
      have hle : ((k * n : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast hlt
      have hknM : ((k * n : ℕ) : ℝ) ≤ M := by exact_mod_cast (hlt.le.trans hmM)
      have : ((k * n : ℕ) : ℝ) / M ≤ 1 := (div_le_one hM).mpr hknM
      calc ((k * n : ℕ) : ℝ) * (1 + 1 / M) = ((k * n : ℕ) : ℝ) + ((k * n : ℕ) : ℝ) / M := by ring
        _ ≤ m := by linarith
    have h2 : Real.log (1 + 1 / M) ≤ Real.log m - Real.log ((k * n : ℕ) : ℝ) := by
      rw [← Real.log_div hmr.ne' hkn.ne']
      exact Real.log_le_log (by positivity) ((le_div_iff₀ hkn).mpr (by linarith))
    rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 1 + 1 / M by
      have : (0 : ℝ) ≤ 1 / M := by positivity
      linarith)])] at h
    linarith
  · -- `kn ≥ m + 1`: then `kn/m ≥ 1 + 1/M`
    have h1 : (m : ℝ) * (1 + 1 / M) ≤ ((k * n : ℕ) : ℝ) := by
      have hle : (m : ℝ) + 1 ≤ ((k * n : ℕ) : ℝ) := by exact_mod_cast hgt
      have : (m : ℝ) / M ≤ 1 := (div_le_one hM).mpr (by exact_mod_cast hmM)
      calc (m : ℝ) * (1 + 1 / M) = m + m / M := by ring
        _ ≤ _ := by linarith
    have h2 : Real.log (1 + 1 / M) ≤ Real.log ((k * n : ℕ) : ℝ) - Real.log m := by
      rw [← Real.log_div hkn.ne' hmr.ne']
      exact Real.log_le_log (by positivity) ((le_div_iff₀ hmr).mpr (by linarith))
    rw [abs_of_nonneg (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ 1 + 1 / M by
      have : (0 : ℝ) ≤ 1 / M := by positivity
      linarith)])] at h
    linarith

/-! ### The autocorrelation at the integer lags -/

/-- Hypotheses of a log-atom test: a `C²` bump of width `δ < log(1 + 1/M)` and orders in `[1, M]`. -/
structure LogAtomData (φ : ℝ → ℝ) (δ : ℝ) (S : Finset ℕ) (M : ℕ) : Prop where
  contDiff : ContDiff ℝ 2 φ
  support : ∀ u, δ / 2 < |u| → φ u = 0
  narrow : δ < Real.log (1 + 1 / M)
  pos : ∀ n ∈ S, 0 < n
  le : ∀ n ∈ S, n ≤ M

/-- At the lag `log k` the autocorrelation counts the pairs with `m = kn`. -/
theorem logAtomAutocorr_log {S : Finset ℕ} {M : ℕ} (hd : LogAtomData φ δ S M) (x : ℕ → ℝ)
    {k : ℕ} (hk : 0 < k) :
    logAtomAutocorr φ S x (Real.log k) =
      (∫ u, φ u ^ 2) * ∑ m ∈ S, ∑ n ∈ S, x m * x n * (if k * n = m then 1 else 0) := by
  rw [logAtomAutocorr_eq hd.contDiff hd.support, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  rw [mul_sum]
  refine sum_congr rfl fun n hn => ?_
  split_ifs with hkn
  · have hc : Real.log k + Real.log n = Real.log m := by
      rw [← Real.log_mul (by exact_mod_cast hk.ne') (by exact_mod_cast (hd.pos n hn).ne'), ← hkn,
        Nat.cast_mul]
    rw [hc]
    have : ∫ u, φ (u - Real.log m) * φ (u - Real.log m) = ∫ u, φ u ^ 2 := by
      rw [integral_sub_right_eq_self (fun u => φ u * φ u) (Real.log m)]
      simp only [sq]
    rw [this]; ring
  · have hfar : δ < |Real.log m - (Real.log k + Real.log n)| := by
      by_contra hle
      push Not at hle
      apply hkn
      refine eq_of_abs_log_sub_lt hk (hd.pos m hm) (hd.pos n hn) (hd.le m hm) ?_
      rw [show Real.log k - (Real.log m - Real.log n) = -(Real.log m - (Real.log k + Real.log n))
        by ring, abs_neg]
      exact hle.trans_lt hd.narrow
    have hz : (fun u => φ (u - Real.log m) * φ (u - (Real.log k + Real.log n))) = fun _ => 0 :=
      funext fun u => RHTower.SeparatedBump.mul_translate_eq_zero hd.support hfar u
    rw [hz, integral_zero]; ring

/-- At the lag `−log k` the autocorrelation counts the pairs with `n = km`. -/
theorem logAtomAutocorr_neg_log {S : Finset ℕ} {M : ℕ} (hd : LogAtomData φ δ S M) (x : ℕ → ℝ)
    {k : ℕ} (hk : 0 < k) :
    logAtomAutocorr φ S x (-Real.log k) =
      (∫ u, φ u ^ 2) * ∑ m ∈ S, ∑ n ∈ S, x m * x n * (if k * m = n then 1 else 0) := by
  have hsymm : logAtomAutocorr φ S x (-Real.log k) = logAtomAutocorr φ S x (Real.log k) := by
    unfold logAtomAutocorr
    rw [← integral_sub_right_eq_self _ (Real.log k)]
    congr 1; funext u
    rw [show u - Real.log k - -Real.log k = u by ring, mul_comm]
  rw [hsymm, logAtomAutocorr_log hd x hk, sum_comm]
  congr 1
  exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring

/-! ### The prime functional -/

/-- Weil's prime functional `Σ_k Λ(k) k^{−1/2} (A(log k) + A(−log k))` at a real lag function `A`. -/
def primeSum (A : ℝ → ℝ) : ℝ :=
  ∑' k : ℕ, Λ k / Real.sqrt k * (A (Real.log k) + A (-Real.log k))

/-- The prime weights seen by an ordered pair: `Σ_k Λ(k) k^{−1/2}([kn = m] + [km = n]) = P(m, n)`. -/
theorem tsum_pair_eq_weilPrimeKernel {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∑' k : ℕ, Λ k / Real.sqrt k * ((if k * n = m then 1 else 0) + (if k * m = n then 1 else 0)) =
      weilPrimeKernel m n := by
  by_cases hmn : m = n
  · subst hmn
    rw [tsum_congr (g := fun _ => (0 : ℝ)) fun k => ?_, tsum_zero]
    · simp [weilPrimeKernel]
    · by_cases hk : k = 1
      · subst hk; simp
      · have : ¬ k * m = m := fun h => hk (by
          have := Nat.eq_of_mul_eq_mul_right hm (h.trans (one_mul m).symm); exact this)
        simp [this]
  by_cases hnm : n ∣ m
  · have hlt : n < m := lt_of_le_of_ne (Nat.le_of_dvd hm hnm) (Ne.symm hmn)
    rw [tsum_eq_single (m / n)]
    · rw [if_pos (Nat.div_mul_cancel hnm), if_neg (by
        intro h
        have : m / n * m ≥ m := Nat.le_mul_of_pos_left m (Nat.div_pos hlt.le hn)
        omega), add_zero, mul_one, weilPrimeKernel,
        if_neg (fun h => by have := Nat.le_of_dvd hn h.1; omega), if_pos ⟨hnm, Ne.symm hmn⟩]
    · intro k hk
      rw [if_neg (fun h => hk (by rw [← h, Nat.mul_div_cancel _ hn])), if_neg (by
        intro h
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · simp at h; omega
        · have : k * m ≥ m := Nat.le_mul_of_pos_left m hk0
          omega)]
      simp
  by_cases hmd : m ∣ n
  · have hlt : m < n := lt_of_le_of_ne (Nat.le_of_dvd hn hmd) hmn
    rw [tsum_eq_single (n / m)]
    · rw [if_neg (by
        intro h
        have : n / m * n ≥ n := Nat.le_mul_of_pos_left n (Nat.div_pos hlt.le hm)
        omega), if_pos (Nat.div_mul_cancel hmd), zero_add, mul_one, weilPrimeKernel,
        if_pos ⟨hmd, hmn⟩]
    · intro k hk
      rw [if_neg (by
        intro h
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · simp at h; omega
        · have : k * n ≥ n := Nat.le_mul_of_pos_left n hk0
          omega), if_neg (fun h => hk (by rw [← h, Nat.mul_div_cancel _ hm]))]
      simp
  · rw [tsum_congr (g := fun _ => (0 : ℝ)) fun k => ?_, tsum_zero]
    · simp [weilPrimeKernel, hmd, hnm]
    · rw [if_neg (fun h => hnm ⟨k, by rw [← h, mul_comm]⟩),
        if_neg (fun h => hmd ⟨k, by rw [← h, mul_comm]⟩)]
      simp

/-- **Weil's prime functional on log-atom tests is the finite intersection pairing**:
`Σ_k Λ(k)k^{−1/2}(A(log k) + A(−log k)) = ‖φ‖² Σ_{m,n ∈ S} x_m x_n P(m, n)`. -/
theorem primeSum_logAtom_eq {S : Finset ℕ} {M : ℕ} (hd : LogAtomData φ δ S M) (x : ℕ → ℝ) :
    primeSum (logAtomAutocorr φ S x) = (∫ u, φ u ^ 2) * primeForm S x := by
  have hterm : ∀ k : ℕ, Λ k / Real.sqrt k *
      (logAtomAutocorr φ S x (Real.log k) + logAtomAutocorr φ S x (-Real.log k)) =
      (∫ u, φ u ^ 2) * ∑ m ∈ S, ∑ n ∈ S, x m * x n * (Λ k / Real.sqrt k *
        ((if k * n = m then 1 else 0) + (if k * m = n then 1 else 0))) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    rw [logAtomAutocorr_log hd x hk, logAtomAutocorr_neg_log hd x hk, ← mul_add, ← sum_add_distrib,
      mul_left_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    ring
  -- each pair contributes a finitely supported series
  have hsum : ∀ m ∈ S, ∀ n ∈ S, Summable fun k : ℕ => x m * x n * (Λ k / Real.sqrt k *
      ((if k * n = m then 1 else 0) + (if k * m = n then 1 else 0))) := by
    intro m hm n hn
    have hm0 := hd.pos m hm
    have hn0 := hd.pos n hn
    refine summable_of_ne_finset_zero (s := range (m + n + 1)) fun k hk => ?_
    rw [mem_range, not_lt] at hk
    have h1 : ¬ k * n = m := fun h => by
      have : k ≤ k * n := Nat.le_mul_of_pos_right k hn0
      omega
    have h2 : ¬ k * m = n := fun h => by
      have : k ≤ k * m := Nat.le_mul_of_pos_right k hm0
      omega
    simp [h1, h2]
  unfold primeSum
  simp_rw [hterm]
  rw [tsum_mul_left, Summable.tsum_finsetSum fun m hm => summable_sum fun n hn => hsum m hm n hn]
  unfold primeForm
  congr 1
  refine sum_congr rfl fun m hm => ?_
  rw [Summable.tsum_finsetSum fun n hn => hsum m hm n hn]
  refine sum_congr rfl fun n hn => ?_
  rw [tsum_mul_left, tsum_pair_eq_weilPrimeKernel (hd.pos m hm) (hd.pos n hn)]

/-- **The prime functional is the sum of the transverse tower forms.** -/
theorem primeSum_logAtom_eq_towers {S : Finset ℕ} {M : ℕ} (hd : LogAtomData φ δ S M)
    (x : ℕ → ℝ) :
    primeSum (logAtomAutocorr φ S x) =
      (∫ u, φ u ^ 2) * ∑ p ∈ (∏ n ∈ S, n).primeFactors, localForm S x p := by
  rw [primeSum_logAtom_eq hd, primeForm_eq_sum_localForm S x fun n hn => (hd.pos n hn).ne']

/-! ### Weil's explicit formula on log-atom tests -/

/-- The archimedean and polar part of Weil's explicit formula. -/
def archPolarPart (k : ℝ → ℂ) : ℂ :=
  Zeta23.paperFT k (I / 2) + Zeta23.paperFT k (-I / 2) +
    (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ)

/-- `W = archimedean + polar part − prime part`. -/
theorem literatureRHS_eq_archPolar_sub_prime (k : ℝ → ℂ) :
    Zeta23.EF.literatureRHS k = archPolarPart k -
      ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
  unfold Zeta23.EF.literatureRHS archPolarPart
  ring

theorem weilTest_logAtom (S : Finset ℕ) (x : ℕ → ℝ) (y : ℝ) :
    Zeta23.EF.weilTest (fun u => (logAtomTest φ S x u : ℂ)) (fun u => (logAtomTest φ S x u : ℂ)) y =
      (logAtomAutocorr φ S x y : ℂ) := by
  rw [RHTower.SeparatedBump.weilTest_ofReal_apply, logAtomAutocorr, integral_complex_ofReal]

theorem contDiff_logAtomTest (hφ : ContDiff ℝ 2 φ) (S : Finset ℕ) (x : ℕ → ℝ) :
    ContDiff ℝ 2 (logAtomTest φ S x) := by
  unfold logAtomTest
  exact ContDiff.sum fun n _ => contDiff_const.mul (hφ.comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_logAtomTest (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (S : Finset ℕ)
    (x : ℕ → ℝ) : HasCompactSupport (logAtomTest φ S x) := by
  refine RHTower.SeparatedBump.hasCompactSupport_of_abs_gt
    (R := ∑ n ∈ S, |Real.log n| + δ / 2) fun u hu => ?_
  refine sum_eq_zero fun n hn => ?_
  have hle : |Real.log n| ≤ ∑ m ∈ S, |Real.log m| :=
    single_le_sum (f := fun m : ℕ => |Real.log m|) (fun _ _ => abs_nonneg _) hn
  rw [RHTower.SeparatedBump.translate_eq_zero hφs (Real.log n) (by linarith), mul_zero]

/-- **Hodge index in tower form, under RH.** For every log-atom cycle, the archimedean and polar part
of Weil's explicit formula dominates `‖φ‖²` times the sum of the transverse tower forms. -/
theorem riemannHypothesis_archPolar_ge_towers (hRH : RiemannHypothesis) {S : Finset ℕ} {M : ℕ}
    (hd : LogAtomData φ δ S M) (x : ℕ → ℝ) :
    (∫ u, φ u ^ 2) * ∑ p ∈ (∏ n ∈ S, n).primeFactors, localForm S x p ≤
      (archPolarPart (Zeta23.EF.weilTest (fun u => (logAtomTest φ S x u : ℂ))
        (fun u => (logAtomTest φ S x u : ℂ)))).re := by
  have hW := (literatureRHS_weilTest_eq_criticalWeilEnergy_of_riemannHypothesis hRH
    (contDiff_logAtomTest hd.contDiff S x) (hasCompactSupport_logAtomTest hd.support S x)).2
  rw [literatureRHS_eq_archPolar_sub_prime, sub_re] at hW
  have hprime : (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) *
      (Zeta23.EF.weilTest (fun u => (logAtomTest φ S x u : ℂ))
        (fun u => (logAtomTest φ S x u : ℂ)) (Real.log n) +
       Zeta23.EF.weilTest (fun u => (logAtomTest φ S x u : ℂ))
        (fun u => (logAtomTest φ S x u : ℂ)) (-Real.log n))).re =
      primeSum (logAtomAutocorr φ S x) := by
    simp only [weilTest_logAtom]
    rw [primeSum]
    have : (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((logAtomAutocorr φ S x (Real.log n) : ℂ) + (logAtomAutocorr φ S x (-Real.log n) : ℂ))) =
        fun n => ((Λ n / Real.sqrt n * (logAtomAutocorr φ S x (Real.log n) +
          logAtomAutocorr φ S x (-Real.log n)) : ℝ) : ℂ) := by
      funext n; push_cast; ring
    rw [this, ← ofReal_tsum, ofReal_re]
  rw [hprime, primeSum_logAtom_eq_towers hd] at hW
  linarith

end GaloisForLFunctions.ArithmeticIntersectionTheory
