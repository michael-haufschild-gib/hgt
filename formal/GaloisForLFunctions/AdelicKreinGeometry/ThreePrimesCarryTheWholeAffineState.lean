import GaloisForLFunctions.AdelicKreinGeometry.EveryPadicNeighborhoodCarriesTheWholeAffineState
import Mathlib.FieldTheory.Finite.Basic

/-!
# A fixed three-prime core carries the affine Weil index

Common totient powers of two primes outside `p` lie in every p-adic principal-unit
neighborhood. Their logarithms remain dense, retaining the full Weil index even
on mass-zero families. Correlation oscillation persists at every resolution.

Allowing translations in `ℤ[1/(pqr)]` supplies the expanding sequence `p^(-N)`.
The subgroup gluing formula therefore retains the native affine index `κ+1`
inside this fixed ring, with no unrestricted prime denominators.
-/

noncomputable section

open Complex Finset
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.AdelicKreinGeometry
open GaloisForLFunctions.AdelicKreinGeometry.TowerCoupling

namespace GaloisForLFunctions.AdelicKreinGeometry

/-- Integer divisibility bounds the p-adic norm. -/
private theorem padic_le_of_int_dvd (p k : ℕ) [Fact p.Prime] {z : ℤ}
    (h : (p : ℤ) ^ k ∣ z) :
    Rat.AbsoluteValue.padic p (z : ℚ) ≤ ((p : ℝ)⁻¹) ^ k := by
  obtain ⟨m, rfl⟩ := h
  rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, map_mul, map_pow]
  have hp : Rat.AbsoluteValue.padic p (p : ℚ) = (p : ℝ)⁻¹ := by
    rw [Rat.AbsoluteValue.padic_eq_padicNorm, padicNorm.padicNorm_p_of_prime,
      Rat.cast_inv, Rat.cast_natCast]
  rw [hp]
  apply mul_le_of_le_one_right (by positivity)
  rw [Rat.AbsoluteValue.padic_eq_padicNorm]
  exact_mod_cast padicNorm.of_int (p := p) m

/-- Euler powers satisfy the prescribed principal-unit congruence. -/
theorem prime_power_mem_principal (p q : Nat.Primes) (hpq : p ≠ q)
    (n k : ℕ) (hsmall : ((p : ℝ)⁻¹) ^ k < ((n : ℝ) + 1)⁻¹) :
    letI : Fact (p : ℕ).Prime := ⟨p.2⟩
    primeUnit q ^ ((p : ℕ) ^ k).totient ∈ padicPrincipalUnits p n := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  letI : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hpq' : (p : ℕ) ≠ (q : ℕ) := fun h => hpq (Subtype.ext h)
  have hcop : Nat.Coprime (q : ℕ) ((p : ℕ) ^ k) :=
    ((Nat.coprime_primes q.2 p.2).mpr hpq'.symm).pow_right k
  have hdvd : (p : ℤ) ^ k ∣ (q : ℤ) ^ ((p : ℕ) ^ k).totient - 1 := by
    simpa only [Nat.cast_pow, Nat.cast_one] using (Nat.ModEq.pow_totient hcop).symm.dvd
  constructor
  · change Rat.AbsoluteValue.padic (p : ℕ)
      ((q : ℚ) ^ ((p : ℕ) ^ k).totient) = 1
    rw [map_pow, Rat.AbsoluteValue.padic_eq_padicNorm,
      padicNorm.padicNorm_of_prime_of_ne hpq', Rat.cast_one, one_pow]
  · change Rat.AbsoluteValue.padic (p : ℕ)
      ((q : ℚ) ^ ((p : ℕ) ^ k).totient - 1) < _
    have h := (padic_le_of_int_dvd p k hdvd).trans_lt hsmall
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_one] using h

/-- Two-prime positive slopes satisfying a p-adic principal-unit condition. -/
def twoPrimePrincipalUnits (p q r : Nat.Primes) (n : ℕ) : Subgroup posUnits :=
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  twoPrimeUnits q r ⊓ padicPrincipalUnits p n

/-- A common Euler power sends the entire two-prime group into the principal subgroup. -/
private theorem pow_mem_twoPrimePrincipalUnits (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (n k : ℕ)
    (hsmall : ((p : ℝ)⁻¹) ^ k < ((n : ℝ) + 1)⁻¹)
    (u : twoPrimeUnits q r) :
    (u : posUnits) ^ ((p : ℕ) ^ k).totient ∈ twoPrimePrincipalUnits p q r n := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  refine ⟨(twoPrimeUnits q r).pow_mem u.2 _, ?_⟩
  have h : ∀ v : posUnits, v ∈ twoPrimeUnits q r →
      v ^ ((p : ℕ) ^ k).totient ∈ padicPrincipalUnits p n := by
    intro v hv
    unfold twoPrimeUnits at hv
    induction hv using Subgroup.closure_induction with
    | mem v hv =>
      rcases Set.mem_insert_iff.mp hv with rfl | hv
      · exact prime_power_mem_principal p q hpq n k hsmall
      · rw [Set.mem_singleton_iff.mp hv]
        exact prime_power_mem_principal p r hpr n k hsmall
    | one => simpa only [one_pow] using (padicPrincipalUnits p n).one_mem
    | mul x y _ _ hx hy =>
      rw [mul_pow]
      exact (padicPrincipalUnits p n).mul_mem hx hy
    | inv x _ hx =>
      rw [inv_pow]
      exact (padicPrincipalUnits p n).inv_mem hx
  exact h u u.2

/-- Every principal resolution of the fixed two-prime slope group has dense logarithms. -/
theorem exists_twoPrimePrincipalUnit_log_near (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (n : ℕ)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : twoPrimePrincipalUnits p q r n, |logPos (u : posUnits) - t| < ε := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < ((n : ℝ) + 1)⁻¹) (inv_lt_one_of_one_lt₀ hp)
  let M := ((p : ℕ) ^ k).totient
  have hMnat : 0 < M := Nat.totient_pos.mpr (pow_pos p.2.pos k)
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr hMnat
  obtain ⟨v, hv, u, rfl⟩ := Metric.dense_iff.mp (dense_range_logPos_twoPrimeUnits hqr)
    (t / M) (ε / M) (div_pos hε hM)
  have hu : |logPos (u : posUnits) - t / M| < ε / M := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hv
  let w : twoPrimePrincipalUnits p q r n :=
    ⟨(u : posUnits) ^ M, pow_mem_twoPrimePrincipalUnits p q r hpq hpr n k hk u⟩
  have hw : logPos (w : posUnits) = (M : ℝ) * logPos (u : posUnits) := by
    simpa only [w, zpow_natCast, Int.cast_natCast] using logPos_zpow (u : posUnits) (M : ℤ)
  refine ⟨w, ?_⟩
  calc |logPos (w : posUnits) - t|
      = (M : ℝ) * |logPos (u : posUnits) - t / M| := by
        rw [hw, show (M : ℝ) * logPos (u : posUnits) - t =
          (M : ℝ) * (logPos (u : posUnits) - t / M) by
            rw [mul_sub, mul_div_cancel₀ _ hM.ne'], abs_mul, abs_of_pos hM]
    _ < (M : ℝ) * (ε / M) := mul_lt_mul_of_pos_left hu hM
    _ = ε := mul_div_cancel₀ _ hM.ne'

/-- The rational ring `ℤ[1/(pqr)]`, generated by the three inverse primes. -/
def threePrimeRing (p q r : Nat.Primes) : Subring ℚ :=
  Subring.closure {(p : ℚ)⁻¹, (q : ℚ)⁻¹, (r : ℚ)⁻¹}

/-- Both a two-prime slope and its inverse belong to the fixed localization ring. -/
theorem twoPrimeUnits_mem_ring (p q r : Nat.Primes) {u : posUnits}
    (hu : u ∈ twoPrimeUnits q r) :
    ((u : ℚˣ) : ℚ) ∈ threePrimeRing p q r ∧
      (((u : ℚˣ) : ℚ)⁻¹) ∈ threePrimeRing p q r := by
  unfold twoPrimeUnits at hu
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · change (q : ℚ) ∈ threePrimeRing p q r ∧ (q : ℚ)⁻¹ ∈ threePrimeRing p q r
      exact ⟨natCast_mem (threePrimeRing p q r) _, Subring.subset_closure (by simp)⟩
    · rw [Set.mem_singleton_iff.mp hu]
      change (r : ℚ) ∈ threePrimeRing p q r ∧ (r : ℚ)⁻¹ ∈ threePrimeRing p q r
      exact ⟨natCast_mem (threePrimeRing p q r) _, Subring.subset_closure (by simp)⟩
  | one => simpa only [Subgroup.coe_one, Units.val_one, inv_one] using
      And.intro (threePrimeRing p q r).one_mem (threePrimeRing p q r).one_mem
  | mul x y _ _ hx hy =>
    simp only [Subgroup.coe_mul, Units.val_mul, mul_inv]
    exact ⟨(threePrimeRing p q r).mul_mem hx.1 hy.1,
      (threePrimeRing p q r).mul_mem hx.2 hy.2⟩
  | inv x _ hx =>
    simpa only [Subgroup.coe_inv, Units.val_inv_eq_inv_val, inv_inv] using And.intro hx.2 hx.1

/-- Positive affine maps with slopes in `H` and translations in `R`.
Every slope of `H`, including its inverse, belongs to `R`. -/
def affineOver (R : Subring ℚ) (H : Subgroup posUnits)
    (hR : ∀ u : H, (((u : posUnits) : ℚˣ) : ℚ) ∈ R) : Subgroup AffineGroupQ where
  carrier := {g | g ∈ posAffine ∧ slopeAbs g ∈ H ∧ affShift g ∈ R}
  one_mem' := by
    exact ⟨posAffine.one_mem, by simpa only [map_one] using H.one_mem,
      by simpa only [affShift_one] using R.zero_mem⟩
  mul_mem' {g h} hg hh := by
    refine ⟨posAffine.mul_mem hg.1 hh.1, ?_, ?_⟩
    · rw [map_mul]
      exact H.mul_mem hg.2.1 hh.2.1
    · have hs : affSlope g ∈ R := by
        simpa only [val_slopeAbs, abs_of_pos (show 0 < affSlope g from hg.1)] using hR ⟨slopeAbs g, hg.2.1⟩
      rw [affShift_mul]
      exact R.add_mem (R.mul_mem hs hh.2.2) hg.2.2
  inv_mem' {g} hg := by
    refine ⟨posAffine.inv_mem hg.1, ?_, ?_⟩
    · rw [map_inv]
      exact H.inv_mem hg.2.1
    · have hs : (affSlope g)⁻¹ ∈ R := by
        simpa only [Subgroup.coe_inv, Units.val_inv_eq_inv_val,
          val_slopeAbs, abs_of_pos (show 0 < affSlope g from hg.1)] using hR ⟨(slopeAbs g)⁻¹, H.inv_mem hg.2.1⟩
      rw [affShift_inv, div_eq_mul_inv]
      exact R.mul_mem (R.neg_mem hg.2.2) hs

/-- Principal-unit slopes from two primes and translations in `ℤ[1/(pqr)]`. -/
def threePrimePrincipalAffine (p q r : Nat.Primes) (n : ℕ) : Subgroup AffineGroupQ :=
  affineOver (threePrimeRing p q r) (twoPrimePrincipalUnits p q r n)
    (fun u => (twoPrimeUnits_mem_ring p q r u.2.1).1)

private theorem dilation_mem_threePrimePrincipalAffine (p q r : Nat.Primes) (n : ℕ)
    (u : twoPrimePrincipalUnits p q r n) :
    dilation ((u : posUnits) : ℚˣ) ∈ threePrimePrincipalAffine p q r n := by
  refine ⟨?_, ?_, ?_⟩
  · change 0 < affSlope (dilation ((u : posUnits) : ℚˣ))
    rw [affSlope_dilation]
    exact (u : posUnits).2
  · rw [slopeAbs_dilation]
    exact u.2
  · rw [affShift_dilation]
    exact (threePrimeRing p q r).zero_mem

private theorem translation_mem_threePrimePrincipalAffine (p q r : Nat.Primes) (n : ℕ)
    {t : ℚ} (ht : t ∈ threePrimeRing p q r) :
    translation t ∈ threePrimePrincipalAffine p q r n := by
  refine ⟨?_, ?_, ?_⟩
  · change 0 < affSlope (translation t)
    rw [affSlope_translation]
    exact zero_lt_one
  · rw [slopeAbs_translation]
    exact (twoPrimePrincipalUnits p q r n).one_mem
  · rw [affShift_translation]
    exact ht

/-- The mass-zero Weil index is preserved in every fixed two-prime principal subgroup. -/
theorem polarIndex_ratCorr_twoPrimePrincipalUnits (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (n : ℕ) :
    polarIndex (ratCorr ∘ (twoPrimePrincipalUnits p q r n).subtype) = negIndex ratCorr :=
  polarIndex_ratCorr_of_dense_log _ (exists_twoPrimePrincipalUnit_log_near p q r hpq hpr hqr n)

/-- The full Weil index is preserved in every fixed two-prime principal subgroup. -/
theorem negIndex_ratCorr_twoPrimePrincipalUnits (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (n : ℕ) :
    negIndex (ratCorr ∘ (twoPrimePrincipalUnits p q r n).subtype) = negIndex ratCorr := by
  refine le_antisymm (negIndex_comp_le ratCorr _) ?_
  rw [← polarIndex_ratCorr_twoPrimePrincipalUnits p q r hpq hpr hqr n]
  exact polarIndex_le_negIndex _

/-- Each principal resolution approximates every global correlation value. -/
theorem exists_twoPrimePrincipalUnit_ratCorr_near (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (n : ℕ) (u : posUnits)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : twoPrimePrincipalUnits p q r n, ‖ratCorr v - ratCorr u‖ < ε := by
  have hc : Continuous (fun t : ℝ => splineCorr (-t)) :=
    TowerCoupling.continuous_splineCorr.comp continuous_neg
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := logPos u)) ε hε
  obtain ⟨v, hv⟩ := exists_twoPrimePrincipalUnit_log_near p q r hpq hpr hqr n (logPos u) hδ
  refine ⟨v, ?_⟩
  simpa only [dist_eq_norm, ratCorr] using hclose (by simpa only [Real.dist_eq] using hv)

/-- A fixed positive correlation oscillation persists at every principal resolution. -/
theorem exists_uniform_twoPrime_padic_ratCorr_oscillation (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, ∃ u : twoPrimePrincipalUnits p q r n,
      ε ≤ ‖ratCorr u - ratCorr 1‖ := by
  obtain ⟨v, hv⟩ := exists_ratCorr_ne_identity
  have hpos : 0 < ‖ratCorr v - ratCorr 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
  refine ⟨‖ratCorr v - ratCorr 1‖ / 2, half_pos hpos, fun n => ?_⟩
  obtain ⟨u, hu⟩ := exists_twoPrimePrincipalUnit_ratCorr_near p q r hpq hpr hqr n v (half_pos hpos)
  refine ⟨u, ?_⟩
  have htri := norm_add_le (ratCorr v - ratCorr u) (ratCorr u - ratCorr 1)
  rw [sub_add_sub_cancel, norm_sub_rev (ratCorr v) (ratCorr u)] at htri
  linarith only [htri, hu]

/-- P-adic discontinuity already occurs on two fixed prime slopes. -/
theorem not_padic_continuous_ratCorr_twoPrimeUnits (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    letI : Fact (p : ℕ).Prime := ⟨p.2⟩
    ¬ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ u : twoPrimeUnits q r,
      Rat.AbsoluteValue.padic p ((((u : posUnits) : ℚˣ) : ℚ) - 1) < δ →
        ‖ratCorr u - ratCorr 1‖ < ε) := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  intro hc
  obtain ⟨ε, hε, hosc⟩ := exists_uniform_twoPrime_padic_ratCorr_oscillation p q r hpq hpr hqr
  obtain ⟨δ, hδ, hmod⟩ := hc ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  obtain ⟨u, hu⟩ := hosc n
  have hsmall : Rat.AbsoluteValue.padic p ((((u : posUnits) : ℚˣ) : ℚ) - 1) < δ :=
    u.2.2.2.trans (by simpa only [one_div] using hn)
  exact (not_lt_of_ge hu) (hmod ⟨u, u.2.1⟩ hsmall)

/-- Unit place norms identify the place-polar mass with ordinary total mass. -/
private theorem placeMass_twoPrimePrincipalUnits (p q r : Nat.Primes) (n : ℕ) {m : ℕ}
    (u : Fin m → twoPrimePrincipalUnits p q r n) :
    letI : Fact (p : ℕ).Prime := ⟨p.2⟩
    placeMass (Rat.AbsoluteValue.padic p) 1 (fun i => (u i : posUnits)) = totalMass (Fin m) := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  apply LinearMap.ext
  intro w
  change (∑ i, w i * (((Rat.AbsoluteValue.padic p (((u i : posUnits) : ℚˣ) : ℚ)) ^
    (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = ∑ i, w i
  apply sum_congr rfl
  intro i _
  rw [(u i).2.2.1, Real.one_rpow, Complex.ofReal_one, mul_one]

/-- The native affine Weil state retains all global negative squares and its successor
square inside a fixed three-prime ring, at every principal-unit resolution. -/
theorem negIndex_weilPadicState_threePrimePrincipalAffine (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    letI : Fact (p : ℕ).Prime := ⟨p.2⟩
    negIndex (weilPadicState p c ∘ (threePrimePrincipalAffine p q r n).subtype) =
      negIndex ratCorr + 1 := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  let K := ratCorr ∘ (twoPrimePrincipalUnits p q r n).subtype
  let Φ := weilPadicState p c ∘ (threePrimePrincipalAffine p q r n).subtype
  have hupper : negIndex Φ ≤ negIndex ratCorr + 1 := by
    exact (negIndex_comp_le (weilPadicState p c) (threePrimePrincipalAffine p q r n).subtype).trans
      (by rw [negIndex_weilPadicState_eq p hc, negIndex_ratCorr])
  refine le_antisymm hupper ?_
  have hfamily (m : ℕ) (u : Fin m → twoPrimePrincipalUnits p q r n) :
      (negIndexOn (gram K u) (LinearMap.ker (totalMass (Fin m))) : ℕ∞) + 1 ≤ negIndex Φ := by
    have h := add_one_le_negIndex_glueAt_subgroup_of_translation_powers
      (isGluingSuccessor_negUltra p hc) one_pos isHermKernel_ratCorr
      (fun i => (u i : posUnits)) (threePrimePrincipalAffine p q r n)
      (fun i => dilation_mem_threePrimePrincipalAffine p q r n (u i))
      ⟨(p : ℚ)⁻¹, one_lt_padic_inv p, fun N =>
        translation_mem_threePrimePrincipalAffine p q r n
          ((threePrimeRing p q r).pow_mem (Subring.subset_closure (by simp)) N)⟩
    rw [placeMass_twoPrimePrincipalUnits] at h
    exact h
  rcases eq_or_ne (negIndex Φ) ⊤ with htop | htop
  · rw [htop]
    exact le_top
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp htop
  have hfinite (m : ℕ) (u : Fin m → twoPrimePrincipalUnits p q r n) :
      negIndexOn (gram K u) (LinearMap.ker (totalMass (Fin m))) + 1 ≤ M := by
    have h := hfamily m u
    rw [← hM] at h
    exact_mod_cast h
  have h1 : 1 ≤ M := by
    have h := hfinite 0 (fun i => i.elim0)
    omega
  have hall (m : ℕ) (u : Fin m → twoPrimePrincipalUnits p q r n) :
      (negIndexOn (gram K u) (LinearMap.ker (totalMass (Fin m))) : ℕ∞) ≤ ((M - 1 : ℕ) : ℕ∞) :=
    Nat.cast_le.mpr (by have h := hfinite m u; omega)
  calc negIndex ratCorr + 1 = polarIndex K + 1 := by
        rw [polarIndex_ratCorr_twoPrimePrincipalUnits p q r hpq hpr hqr n]
    _ ≤ ((M - 1 : ℕ) : ℕ∞) + 1 := add_le_add (iSup₂_le hall) le_rfl
    _ = negIndex Φ := by rw [← hM]; norm_cast; omega

end GaloisForLFunctions.AdelicKreinGeometry
