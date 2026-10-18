import GaloisForLFunctions.BezoutValuationIncidence.DilationClockRelativeGapAndSignedComplement

/-!
# Positive signed-complement survival along nearby prime pairs

The exact clock-sector and physical-cutoff costs are bounded by
`2*v*phi(s)^2*(q-p)/p + (PrimitiveBound(r)^2+v*s*phi(s)^2)/p`
when `2 <= p < q <= 2p`, with `s=rad(r)` and `v=r/s`.

Reusing continuity of the actual profile and the existing arbitrarily large
nearby-prime-pair theorem, the data-only capstone places its finite signed
complement arbitrarily close to the positive diagonal Gram while making the
single physical clock-successor sector arbitrarily small. Both quantities
use the same aligned cutoff. This controls a cofinal family of prime pairs;
it does not bound a general signed prime packet.
-/

open Finset RHTower Set Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

/-- In a twofold scale window, the exact physical cutoff and clock-sector costs
are controlled by relative gap plus inverse scale. -/
theorem clock_successor_total_error_le_relative_gap {r p q : ℕ}
    (hr : r ≠ 0) (hp : 1 < p) (hpq : p < q) (hqp : (q : ℝ) ≤ 2 * p) :
    Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        (pmRamanujanPrimitiveBound r ^ 2 /
          ((ramanujanClockSuccessorHorizon r p q : ℝ) + 1)) +
      ramanujanClockSuccessorRelativeGapBudget r p q ≤
      2 * (lagVisibilityClock r : ℝ) * ((primeRadical r).totient : ℝ) ^ 2 *
          ((q : ℝ) - p) / p +
        (pmRamanujanPrimitiveBound r ^ 2 + (lagVisibilityClock r : ℝ) *
          (primeRadical r : ℝ) * ((primeRadical r).totient : ℝ) ^ 2) / p := by
  let s := primeRadical r
  let v := lagVisibilityClock r
  let H := ramanujanClockSuccessorHorizon r p q
  let B := pmRamanujanPrimitiveBound r
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
  have hqR : (0 : ℝ) < q := hpR.trans hpqR
  have hsp := Real.sqrt_nonneg (p : ℝ)
  have hsq := Real.sqrt_nonneg (q : ℝ)
  have hsp0 : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hpR
  have hsple : Real.sqrt (p : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt hpqR.le
  have hwlo : (p : ℝ) ≤ Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) := by
    calc
      _ = Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) := (Real.mul_self_sqrt hpR.le).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsple hsp
  have hwhi : Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) ≤ q := by
    calc
      _ ≤ Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) := mul_le_mul_of_nonneg_right hsple hsq
      _ = _ := Real.mul_self_sqrt hqR.le
  have hratio : Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hsp0).mpr
    nlinarith [Real.sq_sqrt hpR.le, Real.sq_sqrt hqR.le]
  have hvpos : 0 < v :=
    Nat.pos_of_ne_zero fun hz => hr ((lagVisibilityClock_eq_zero_iff r).mp hz)
  have hspos : 0 < s := prod_pos fun _ hx => (Nat.mem_primeFactors.mp hx).1.pos
  have hHnat : p * q ≤ H + 1 := by
    have hsone : 1 ≤ s := by omega
    have hvone : 1 ≤ v := by omega
    have hmul : p * q ≤ p * q * s := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (p * q) hsone
    have hclock : p * q * s + 1 ≤ v * (p * q * s + 1) := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (p * q * s + 1) hvone
    have hfull : 1 ≤ v * (p * q * s + 1) := by omega
    change p * q ≤ v * (p * q * s + 1) - 1 + 1
    rw [Nat.sub_add_cancel hfull]
    omega
  have hH : (p : ℝ) * q ≤ (H : ℝ) + 1 := by exact_mod_cast hHnat
  have hpq0 : (0 : ℝ) < (p : ℝ) * q := mul_pos hpR hqR
  have hcut : Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
      (B ^ 2 / ((H : ℝ) + 1)) ≤ B ^ 2 / p := by
    calc
      _ ≤ (q : ℝ) * (B ^ 2 / ((p : ℝ) * q)) :=
        mul_le_mul hwhi (div_le_div_of_nonneg_left (sq_nonneg B) hpq0 hH)
          (by positivity) (Nat.cast_nonneg q)
      _ = _ := by field_simp [hpR.ne', hqR.ne']
  have hden : (p : ℝ) ≤ (q : ℝ) - 1 := by
    have : (p : ℝ) + 1 ≤ q := by exact_mod_cast (show p + 1 ≤ q by omega)
    linarith
  have habs : |(p : ℝ) - q| = (q : ℝ) - p := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have hseed :
      (v : ℝ) * (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
          ((s.totient : ℝ) ^ 2 * |(p : ℝ) - q| / ((q : ℝ) - 1)) ≤
        2 * (v : ℝ) * (s.totient : ℝ) ^ 2 * ((q : ℝ) - p) / p := by
    rw [habs]
    have hn : 0 ≤ (s.totient : ℝ) ^ 2 * ((q : ℝ) - p) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hpqR.le)
    have hm : (v : ℝ) * (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) ≤ 2 * v := by
      nlinarith [mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg v)]
    calc
      _ ≤ (2 * (v : ℝ)) * ((s.totient : ℝ) ^ 2 * ((q : ℝ) - p) / p) :=
        mul_le_mul hm (div_le_div_of_nonneg_left hn hpR hden)
          (div_nonneg hn (by linarith)) (by positivity)
      _ = _ := by ring
  have htail : (v : ℝ) * ((s : ℝ) * (s.totient : ℝ) ^ 2 /
      (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ))) ≤
      (v : ℝ) * ((s : ℝ) * (s.totient : ℝ) ^ 2 / p) :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by positivity) hpR hwlo) (Nat.cast_nonneg v)
  change _ + (_ + _) ≤ _
  calc
    _ ≤ B ^ 2 / p +
        (2 * (v : ℝ) * (s.totient : ℝ) ^ 2 * ((q : ℝ) - p) / p +
          (v : ℝ) * ((s : ℝ) * (s.totient : ℝ) ^ 2 / p)) :=
      add_le_add hcut (add_le_add hseed htail)
    _ = _ := by dsimp only [B, v, s]; ring

/-- Arbitrarily large nearby prime pairs retain the positive diagonal profile in
the signed complement while their single clock-successor sector becomes small. -/
theorem exists_prime_clock_complement_near_diagonal (r N k : ℕ) :
    let R := r + 2
    let G := pmRamanujanPrimitiveGram R R
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ N < p ∧ p < q ∧
      (q : ℝ) < (1 + 1 / ((k : ℝ) + 1)) * p ∧
      |ramanujanClockSuccessorSector R p q| < G / ((k : ℝ) + 2) ∧
      |ramanujanClockSignedComplement R p q - G| < G / ((k : ℝ) + 2) ∧
      G / 2 < ramanujanClockSignedComplement R p q := by
  let R := r + 2
  have hR : 1 < R := by dsimp only [R]; omega
  let G := pmRamanujanPrimitiveGram R R
  have hG : 0 < G := pmRamanujanPrimitiveGram_pos hR
  let ε := G / ((k : ℝ) + 2)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  let A := 2 * (lagVisibilityClock R : ℝ) * ((primeRadical R).totient : ℝ) ^ 2
  let B := pmRamanujanPrimitiveBound R ^ 2 + (lagVisibilityClock R : ℝ) *
    (primeRadical R : ℝ) * ((primeRadical R).totient : ℝ) ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hc : ContinuousAt (pmRamanujanDilationProfile R hR) 1 :=
    (continuousOn_pmRamanujanDilationProfile hR).continuousAt (Ioi_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (by positivity)
  let η := min (min δ 1) (min (1 / ((k : ℝ) + 1)) (ε / (4 * (A + 1))))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηδ : η ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hη1 : η ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hηk : η ≤ 1 / ((k : ℝ) + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hηε : η ≤ ε / (4 * (A + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  let T := max (N : ℝ) (4 * B / ε)
  obtain ⟨p, q, hp, hq, hTp, hpq, hqp⟩ := exists_prime_pair_ratio_lt hη T
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
  have hNp : N < p := by exact_mod_cast (le_max_left _ _).trans_lt hTp
  have hTpB : 4 * B / ε < (p : ℝ) := (le_max_right _ _).trans_lt hTp
  have hq2 : (q : ℝ) ≤ 2 * p := by
    nlinarith [mul_le_mul_of_nonneg_right hη1 hpR.le]
  have hgap : ((q : ℝ) - p) / p < η := by
    apply (div_lt_iff₀ hpR).mpr
    nlinarith
  have hAη : A * η < ε / 4 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 4 * (A + 1))).mp hηε
    nlinarith
  have hAgap : A * ((q : ℝ) - p) / p < ε / 4 := by
    have hb := mul_le_mul_of_nonneg_left hgap.le hA
    calc
      _ = A * (((q : ℝ) - p) / p) := by ring
      _ ≤ A * η := hb
      _ < _ := hAη
  have hBscale : B / p < ε / 4 := by
    have hb := (div_lt_iff₀ hε).mp hTpB
    apply (div_lt_iff₀ hpR).mpr
    nlinarith
  let E := Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
      (pmRamanujanPrimitiveBound R ^ 2 /
        ((ramanujanClockSuccessorHorizon R p q : ℝ) + 1)) +
    ramanujanClockSuccessorRelativeGapBudget R p q
  have hE : E < ε / 2 := by
    have hb := clock_successor_total_error_le_relative_gap (by omega : R ≠ 0)
      hp.one_lt hpq hq2
    change E ≤ A * ((q : ℝ) - p) / p + B / p at hb
    linarith
  have hbudget : ramanujanClockSuccessorRelativeGapBudget R p q < ε / 2 := by
    have hcut : 0 ≤ Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
        (pmRamanujanPrimitiveBound R ^ 2 /
          ((ramanujanClockSuccessorHorizon R p q : ℝ) + 1)) := by positivity
    dsimp only [E] at hE
    linarith
  have hsector : |ramanujanClockSuccessorSector R p q| < ε :=
    (abs_ramanujanClockSuccessorSector_le_relativeGap (by omega) hp.one_lt hq.one_lt
      (Or.inl hpq)).trans_lt (hbudget.trans (by linarith))
  have happrox : |pmRamanujanDilationProfile R hR ((p : ℝ) / q) -
      ramanujanClockSignedComplement R p q| < ε / 2 :=
    (abs_dilationProfile_sub_clockSignedComplement_le_relativeGap hR hp.one_lt hq.one_lt
      (Or.inl hpq)).trans_lt hE
  have hratio : (p : ℝ) / q < 1 := (div_lt_one hqR).mpr hpqR
  have hratioLower : 1 - η < (p : ℝ) / q := by
    apply (lt_div_iff₀ hqR).mpr
    nlinarith [mul_pos hη (sub_pos.mpr hpqR)]
  have hdist : dist ((p : ℝ) / q) 1 < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hratio.le)]
    linarith
  have hprofile : |pmRamanujanDilationProfile R hR ((p : ℝ) / q) - G| < ε / 2 := by
    simpa only [Real.dist_eq, pmRamanujanDilationProfile_one] using hclose hdist
  have hcomplement : |ramanujanClockSignedComplement R p q - G| < ε := by
    have ht := abs_add_le
      (ramanujanClockSignedComplement R p q - pmRamanujanDilationProfile R hR ((p : ℝ) / q))
      (pmRamanujanDilationProfile R hR ((p : ℝ) / q) - G)
    have he : (ramanujanClockSignedComplement R p q -
        pmRamanujanDilationProfile R hR ((p : ℝ) / q)) +
        (pmRamanujanDilationProfile R hR ((p : ℝ) / q) - G) =
        ramanujanClockSignedComplement R p q - G := by ring
    rw [he, abs_sub_comm (ramanujanClockSignedComplement R p q)
      (pmRamanujanDilationProfile R hR ((p : ℝ) / q))] at ht
    linarith
  have hhalf : ε ≤ G / 2 := by
    exact div_le_div_of_nonneg_left hG.le (by norm_num)
      (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  refine ⟨p, q, hp, hq, hNp, hpq, ?_, hsector, hcomplement, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hηk hpR.le]
  · have := (abs_lt.mp hcomplement).1
    linarith

end
end GaloisForLFunctions.BezoutValuationIncidence

