import GaloisForLFunctions.RHTower.ArithmeticPrimeSievePhase
import Mathlib.Data.Nat.PrimeFin

/-!
# Coprime observations and prime-depth information

Coprime tests distinguish the set of prime divisors of an index but cannot distinguish
exponents of those primes. A nonzero transfer between two positive indices is invisible
to every coprime modulus exactly when their prime-divisor sets agree. Divisibility tests,
which retain prime powers, distinguish every pair of different indices.

Applied to the normalized ordinary remainder, transferring an arbitrary complex amount
from coefficient four to coefficient two preserves every coprime observation, the unit
coefficient, and the complete eventual tail. The fourth-multiple observation changes by
the negative transfer amplitude. The perturbed sequence is an auxiliary sequence, not
another ordinary zeta remainder.

Finite divisor inversion also recovers every original Möbius-weighted modulus term
from the literal coprime-sieve family. The two complete arithmetic records are therefore
mutually reconstructible. These identities supply no independent zero-location law.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- A complex transfer between two positive-index coefficients. -/
def coefficientTransfer (a b : ℕ+) (z : ℂ) (n : ℕ+) : ℂ :=
  (if n = a then z else 0) - (if n = b then z else 0)

/-- The entire coprime observation of an arbitrary coefficient sequence. -/
def coprimeObservation (f : ℕ+ → ℂ) (M : ℕ) : ℂ :=
  ∑' n : ℕ+, if M.Coprime (n : ℕ) then f n else 0

private theorem summable_pointMass (a : ℕ+) (z : ℂ) :
    Summable (fun n : ℕ+ => if n = a then z else 0) := by
  classical
  apply summable_of_ne_finset_zero (s := {a})
  intro n hn
  have h : n ≠ a := by simpa only [Finset.mem_singleton] using hn
  simp only [if_neg h]

/-- Every two-point transfer is absolutely summable. -/
private theorem summable_coefficientTransfer (a b : ℕ+) (z : ℂ) :
    Summable (coefficientTransfer a b z) :=
  (summable_pointMass a z).sub (summable_pointMass b z)

private theorem coprimeObservation_pointMass (a : ℕ+) (z : ℂ) (M : ℕ) :
    coprimeObservation (fun n => if n = a then z else 0) M =
      if M.Coprime (a : ℕ) then z else 0 := by
  classical
  unfold coprimeObservation
  have he : (fun n : ℕ+ => if M.Coprime (n : ℕ) then (if n = a then z else 0) else 0) =
      (fun n : ℕ+ => if n = a then (if M.Coprime (a : ℕ) then z else 0) else 0) := by
    funext n
    by_cases h : n = a
    · subst n
      rw [if_pos (show a=a from rfl), if_pos (show a=a from rfl)]
    · simp [h]
  rw [he, tsum_ite_eq]

private theorem summable_coprimeObservation {f : ℕ+ → ℂ} (hf : Summable f) (M : ℕ) :
    Summable (fun n : ℕ+ => if M.Coprime (n : ℕ) then f n else 0) :=
  (hf.indicator {n : ℕ+ | M.Coprime (n : ℕ)}).congr (fun n => by simp [Set.indicator_apply])

private theorem coprimeObservation_sub {f g : ℕ+ → ℂ} (hf : Summable f) (hg : Summable g)
    (M : ℕ) : coprimeObservation (fun n => f n - g n) M =
      coprimeObservation f M - coprimeObservation g M := by
  unfold coprimeObservation
  calc
    _ = ∑' n : ℕ+, ((if M.Coprime (n : ℕ) then f n else 0) -
        (if M.Coprime (n : ℕ) then g n else 0)) := by
      apply tsum_congr
      intro n
      split_ifs <;> ring
    _ = _ := (summable_coprimeObservation hf M).tsum_sub (summable_coprimeObservation hg M)

/-- One coprime test reads only whether it includes each endpoint of the transfer. -/
private theorem coprimeObservation_coefficientTransfer (a b : ℕ+) (z : ℂ) (M : ℕ) :
    coprimeObservation (coefficientTransfer a b z) M =
      (if M.Coprime (a : ℕ) then z else 0) - (if M.Coprime (b : ℕ) then z else 0) := by
  change coprimeObservation (fun n => (if n=a then z else 0) - (if n=b then z else 0)) M = _
  rw [coprimeObservation_sub (summable_pointMass a z)
    (summable_pointMass b z), coprimeObservation_pointMass, coprimeObservation_pointMass]

private theorem same_coprime_tests_iff (a b : ℕ+) :
    (∀ M : ℕ+, (M : ℕ).Coprime (a : ℕ) ↔ (M : ℕ).Coprime (b : ℕ)) ↔
      (a : ℕ).primeFactors = (b : ℕ).primeFactors := by
  constructor
  · intro h
    ext p
    constructor
    · intro ha
      obtain ⟨hp,hpa,-⟩ := Nat.mem_primeFactors.mp ha
      apply Nat.mem_primeFactors.mpr
      refine ⟨hp, ?_, b.pos.ne'⟩
      by_contra hpb
      have hb := hp.coprime_iff_not_dvd.mpr hpb
      have ha := (h ⟨p,hp.pos⟩).mpr hb
      exact (hp.coprime_iff_not_dvd.mp ha) hpa
    · intro hb
      obtain ⟨hp,hpb,-⟩ := Nat.mem_primeFactors.mp hb
      apply Nat.mem_primeFactors.mpr
      refine ⟨hp, ?_, a.pos.ne'⟩
      by_contra hpa
      have ha := hp.coprime_iff_not_dvd.mpr hpa
      have hb := (h ⟨p,hp.pos⟩).mp ha
      exact (hp.coprime_iff_not_dvd.mp hb) hpb
  · intro h M
    rw [← Nat.disjoint_primeFactors M.pos.ne' a.pos.ne',
      ← Nat.disjoint_primeFactors M.pos.ne' b.pos.ne', h]

/-- A nonzero two-point transfer is invisible to every positive coprime modulus exactly when
its endpoints have the same prime-divisor support. -/
theorem coefficientTransfer_invisible_iff (a b : ℕ+) {z : ℂ} (hz : z ≠ 0) :
    (∀ M : ℕ+, coprimeObservation (coefficientTransfer a b z) M = 0) ↔
      (a : ℕ).primeFactors = (b : ℕ).primeFactors := by
  rw [← same_coprime_tests_iff]
  constructor
  · intro h M
    have he := h M
    rw [coprimeObservation_coefficientTransfer] at he
    constructor
    · intro ha
      by_contra hb
      rw [if_pos ha, if_neg hb, sub_zero] at he
      exact hz he
    · intro hb
      by_contra ha
      rw [if_neg ha, if_pos hb, zero_sub, neg_eq_zero] at he
      exact hz he
  · intro h M
    rw [coprimeObservation_coefficientTransfer]
    by_cases ha : (M : ℕ).Coprime (a : ℕ)
    · rw [if_pos ha, if_pos ((h M).mp ha), sub_self]
    · rw [if_neg ha, if_neg (fun hb => ha ((h M).mpr hb)), sub_self]

/-- A prime and its square have indistinguishable coprime observations. -/
private theorem coprimeObservation_two_four_transfer (z : ℂ) (M : ℕ) :
    coprimeObservation (coefficientTransfer 2 4 z) M = 0 := by
  rw [coprimeObservation_coefficientTransfer]
  have hc : M.Coprime 4 ↔ M.Coprime 2 := by
    simpa only [show (2 : ℕ)^(2 : ℕ) = 4 by norm_num] using Nat.coprime_pow_right_iff (by omega : 0<2) M 2
  change (if M.Coprime 2 then z else 0) - (if M.Coprime 4 then z else 0) = 0
  by_cases h : M.Coprime 2
  · rw [if_pos h, if_pos (hc.mpr h), sub_self]
  · rw [if_neg h, if_neg (fun h4 => h (hc.mp h4)), sub_self]

private theorem coprimeObservation_add {f g : ℕ+ → ℂ} (hf : Summable f) (hg : Summable g)
    (M : ℕ) : coprimeObservation (fun n => f n + g n) M =
      coprimeObservation f M + coprimeObservation g M := by
  unfold coprimeObservation
  calc
    _ = ∑' n : ℕ+, ((if M.Coprime (n : ℕ) then f n else 0) +
        (if M.Coprime (n : ℕ) then g n else 0)) := by
      apply tsum_congr
      intro n
      split_ifs <;> ring
    _ = _ := (summable_coprimeObservation hf M).tsum_add (summable_coprimeObservation hg M)

/-- A finite redistribution of the literal normalized remainder, retaining the unit and tail. -/
def redistributedRemainder (s z : ℂ) (n : ℕ) : ℂ :=
  normalizedWeightedRemainder s n +
    ((if n = 2 then z else 0) - (if n = 4 then z else 0))

private theorem redistribution_eq_transfer (s z : ℂ) (n : ℕ+) :
    redistributedRemainder s z n = normalizedWeightedRemainder s n + coefficientTransfer 2 4 z n := by
  simp only [redistributedRemainder, coefficientTransfer, ← PNat.coe_inj, PNat.val_ofNat]

private theorem summable_literal_normalizedRemainder {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Summable (fun n : ℕ+ => normalizedWeightedRemainder s n) := by
  have hh := (summable_norm_weightedPowerRemainder_pair hs hs1 (m := 1) (by omega)).prod_factor (1 : ℕ+)
  have h : Summable (fun n : ℕ+ => weightedPowerRemainder s n) := by
    apply Summable.of_norm
    simpa only [PNat.val_ofNat, Nat.one_mul] using hh
  exact h.div_const _

/-- The perturbed family remains absolutely summable on the whole admitted half-plane. -/
private theorem summable_redistributedRemainder {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (z : ℂ) :
    Summable (fun n : ℕ+ => redistributedRemainder s z n) := by
  simpa only [redistribution_eq_transfer] using
    (summable_literal_normalizedRemainder hs hs1).add (summable_coefficientTransfer 2 4 z)

/-- Every modulus, not just a fixed finite selection, has exactly the original sieve value. -/
theorem coprimeObservation_redistributedRemainder {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (z : ℂ) (M : ℕ) :
    coprimeObservation (fun n : ℕ+ => redistributedRemainder s z n) M = coprimeRemainder s M := by
  simp_rw [redistribution_eq_transfer]
  rw [coprimeObservation_add (summable_literal_normalizedRemainder hs hs1)
    (summable_coefficientTransfer 2 4 z), coprimeObservation_two_four_transfer, add_zero]
  rfl

/-- The full recovered unit coefficient is preserved, including both complex components. -/
private theorem redistributedRemainder_one (s z : ℂ) :
    redistributedRemainder s z 1 = normalizedWeightedRemainder s 1 := by
  norm_num [redistributedRemainder]

/-- The amplitude of the hidden redistribution is visible in the coefficient at two. -/
private theorem redistributedRemainder_two (s z : ℂ) :
    redistributedRemainder s z 2 = normalizedWeightedRemainder s 2 + z := by
  norm_num [redistributedRemainder]

/-- The finite perturbation does not alter any sufficiently late coefficient. -/
private theorem redistributedRemainder_eq_eventually (s z : ℂ) :
    ∀ᶠ n : ℕ in atTop, redistributedRemainder s z n = normalizedWeightedRemainder s n := by
  filter_upwards [eventually_gt_atTop 4] with n hn
  simp [redistributedRemainder, show n≠2 by omega, show n≠4 by omega]

/-- Even the exact scaled first coefficient survives every complex redistribution amplitude. -/
theorem tendsto_redistributedRemainder_scaled {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (z : ℂ) :
    Tendsto (fun n : ℕ => redistributedRemainder s z n *
      (((n : ℝ)^(2*s.re+1):ℝ):ℂ)) atTop (𝓝 (-(star s+1)⁻¹/12)) := by
  apply (tendsto_normalizedWeightedRemainder_scaled hs hs1).congr'
  filter_upwards [redistributedRemainder_eq_eventually s z] with n hn
  rw [hn]

/-- Prescribing a coefficient at two leaves every coprime observation, the unit coefficient,
and the complete eventual tail unchanged. The new sequence is not asserted to be a zeta remainder. -/
theorem exists_redistribution_with_prescribed_coefficient {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (w : ℂ) : ∃ f : ℕ → ℂ,
      Summable (fun n : ℕ+ => f n) ∧
      (∀ M : ℕ, coprimeObservation (fun n : ℕ+ => f n) M = coprimeRemainder s M) ∧
      f 1 = normalizedWeightedRemainder s 1 ∧
      (∀ᶠ n : ℕ in atTop, f n = normalizedWeightedRemainder s n) ∧ f 2 = w := by
  refine ⟨redistributedRemainder s (w-normalizedWeightedRemainder s 2),
    summable_redistributedRemainder hs hs1 _,
    coprimeObservation_redistributedRemainder hs hs1 _,
    redistributedRemainder_one s _, redistributedRemainder_eq_eventually s _, ?_⟩
  rw [redistributedRemainder_two]
  ring

/-- A divisibility observation retains the exponent of each prime in its modulus. -/
def divisibilityObservation (f : ℕ+ → ℂ) (d : ℕ) : ℂ :=
  ∑' n : ℕ+, if d ∣ (n : ℕ) then f n else 0

private theorem masked_transfer_sum (P : ℕ+ → Prop) [DecidablePred P] (a b : ℕ+) (z : ℂ) :
    (∑' n : ℕ+, if P n then coefficientTransfer a b z n else 0) =
      (if P a then z else 0) - (if P b then z else 0) := by
  classical
  have he : (fun n : ℕ+ => if P n then coefficientTransfer a b z n else 0) =
      (fun n : ℕ+ => (if n=a then (if P a then z else 0) else 0) -
        (if n=b then (if P b then z else 0) else 0)) := by
    funext n
    by_cases ha : n=a
    · subst n
      by_cases hb : a=b
      · subst b
        simp [coefficientTransfer]
      · unfold coefficientTransfer
        rw [if_pos (show a=a from rfl), if_neg hb,
          if_pos (show a=a from rfl), if_neg hb]
        split_ifs <;> ring
    · by_cases hb : n=b
      · subst n
        unfold coefficientTransfer
        rw [if_neg ha, if_pos (show b=b from rfl),
          if_neg ha, if_pos (show b=b from rfl)]
        split_ifs <;> ring
      · simp only [coefficientTransfer, if_neg ha, if_neg hb, sub_self, ite_self]
  rw [he, (summable_pointMass a (if P a then z else 0)).tsum_sub
    (summable_pointMass b (if P b then z else 0)), tsum_ite_eq, tsum_ite_eq]

/-- A divisibility test measures a two-point transfer by its exact threshold indicators. -/
private theorem divisibilityObservation_coefficientTransfer (a b : ℕ+) (z : ℂ) (d : ℕ) :
    divisibilityObservation (coefficientTransfer a b z) d =
      (if d ∣ (a : ℕ) then z else 0) - (if d ∣ (b : ℕ) then z else 0) :=
  masked_transfer_sum (fun n => d ∣ (n : ℕ)) a b z

/-- Unlike coprime tests, the full divisibility family distinguishes every pair of indices. -/
theorem coefficientTransfer_divisibility_invisible_iff (a b : ℕ+) {z : ℂ} (hz : z ≠ 0) :
    (∀ d : ℕ+, divisibilityObservation (coefficientTransfer a b z) d = 0) ↔ a=b := by
  constructor
  · intro h
    have ha := h a
    have hb := h b
    rw [divisibilityObservation_coefficientTransfer, if_pos (dvd_refl _)] at ha
    rw [divisibilityObservation_coefficientTransfer, if_pos (dvd_refl _)] at hb
    have hab : (a : ℕ) ∣ (b : ℕ) := by
      by_contra hn
      rw [if_neg hn, sub_zero] at ha
      exact hz ha
    have hba : (b : ℕ) ∣ (a : ℕ) := by
      by_contra hn
      rw [if_neg hn, zero_sub, neg_eq_zero] at hb
      exact hz hb
    exact PNat.eq (Nat.dvd_antisymm hab hba)
  · rintro rfl d
    rw [divisibilityObservation_coefficientTransfer, sub_self]

/-- The first prime-depth test missed by coprime sieving sees the complete transfer amplitude. -/
private theorem divisibilityObservation_two_four_transfer (z : ℂ) :
    divisibilityObservation (coefficientTransfer 2 4 z) 4 = -z := by
  rw [divisibilityObservation_coefficientTransfer]
  norm_num

private theorem summable_divisibilityObservation {f : ℕ+ → ℂ} (hf : Summable f) (d : ℕ) :
    Summable (fun n : ℕ+ => if d ∣ (n : ℕ) then f n else 0) :=
  (hf.indicator {n : ℕ+ | d ∣ (n : ℕ)}).congr (fun n => by simp [Set.indicator_apply])

private theorem divisibilityObservation_add {f g : ℕ+ → ℂ} (hf : Summable f) (hg : Summable g)
    (d : ℕ) : divisibilityObservation (fun n => f n + g n) d =
      divisibilityObservation f d + divisibilityObservation g d := by
  unfold divisibilityObservation
  calc
    _ = ∑' n : ℕ+, ((if d ∣ (n : ℕ) then f n else 0) +
        (if d ∣ (n : ℕ) then g n else 0)) := by
      apply tsum_congr
      intro n
      split_ifs <;> ring
    _ = _ := (summable_divisibilityObservation hf d).tsum_add
      (summable_divisibilityObservation hg d)

/-- The ordinary source and its sieve-indistinguishable perturbation differ in their
actual fourth-multiple sum by exactly the transfer amplitude. -/
theorem divisibilityObservation_redistributedRemainder_four {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (z : ℂ) :
    divisibilityObservation (fun n : ℕ+ => redistributedRemainder s z n) 4 =
      divisibilityObservation (fun n : ℕ+ => normalizedWeightedRemainder s n) 4 - z := by
  simp_rw [redistribution_eq_transfer]
  rw [divisibilityObservation_add (summable_literal_normalizedRemainder hs hs1)
    (summable_coefficientTransfer 2 4 z), divisibilityObservation_two_four_transfer]
  ring

/-- Finite divisor inversion recovers every original Möbius-weighted modulus term from the
coprime-sieve family. Thus the two full arithmetic records carry identical information. -/
theorem minimumBalanceTerm_eq_finite_sieve_inverse {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) {m : ℕ} (hm : 0 < m) :
    minimumBalanceTerm s m = ∑ d ∈ m.divisorsAntidiagonal,
      (μ d.1 : ℂ) * coprimeRemainder s d.2 := by
  exact ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (fun n hn => (coprimeRemainder_eq_sum_divisors hs hs1 hn.ne').symm)) m hm).symm

end RHTower.DeletionMixedRefinement
