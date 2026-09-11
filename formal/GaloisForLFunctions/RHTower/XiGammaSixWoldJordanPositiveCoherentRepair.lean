import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanCoherentStar
import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanPrimeEscape

/-!
# Prime retention under a positive complete coherent repair

Subtract one complete coherent Frobenius packet from a genuine normalized
fixed-left Big-Witt row. If the repaired coefficients have nonnegative real
parts on every ordered edge, the removed real mass at the anchor is between
zero and `1 / (p * M)`, where `M` is the original raw row mass. The proof uses
both orientations away from the anchor and the largest retained prime.

The literal row mass diverges, so every moving repair in this domain retains
anchor mass tending to one. Its reciprocal energy has real part eventually
at least `A / (2 * p)` for `A > 0` and cannot tend to zero. These source bounds
do not assert the existence of a cyclic-to-physical comparison in this domain
or prove RH. A finite sum of complete packets is outside the one-packet claim.
-/

open Complex Filter Function Set Topology
open scoped BigOperators
namespace RHTower.HedenmalmThetaSource
noncomputable section

/-- Distinct positive prime labels cannot outnumber their largest integer label. -/
theorem primeFinset_card_le_sup (s : Finset Nat.Primes) :
    s.card ≤ s.sup (fun p => (p : ℕ)) := by
  classical
  have h : s.card ≤ (Finset.Icc 1 (s.sup (fun p => (p : ℕ)))).card := by
    apply Finset.card_le_card_of_injOn (fun p : Nat.Primes => (p : ℕ))
    · intro p hp
      exact Finset.mem_Icc.mpr ⟨p.2.pos, Finset.le_sup hp⟩
    · intro p hp q hq hpq
      exact Subtype.ext hpq
  simpa using h

theorem coherentPositiveRepair_profile_re_eq_off_anchor
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) (p : Nat.Primes)
    (hf : ∀ i, i.1.1 ≠ p → (f i).re = 0)
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    (hpos : ∀ i, 0 ≤ (f i - deningerBigWittCrossPairFiniteRightLegPacket a s i).re)
    (q r : Nat.Primes) (hq : q ∈ s) (hr : r ∈ s) (hqp : q ≠ p) (hrp : r ≠ p) :
    (a q).re = (a r).re := by
  by_cases hqr : q = r
  · simp [hqr]
  have h₁ := hpos ⟨(q,r),hqr⟩
  have h₂ := hpos ⟨(r,q),Ne.symm hqr⟩
  rw [Complex.sub_re, hf _ hqp, deningerBigWittCrossPairFiniteRightLegPacket_apply,
    if_pos ⟨hq,hr⟩, deningerBigWittCrossPairRightLeg, Complex.conj_re, Complex.sub_re] at h₁
  rw [Complex.sub_re, hf _ hrp, deningerBigWittCrossPairFiniteRightLegPacket_apply,
    if_pos ⟨hr,hq⟩, deningerBigWittCrossPairRightLeg, Complex.conj_re, Complex.sub_re] at h₂
  linarith

theorem deningerBigWittLeftPrimeMarginal_coherent_re_sum_erase
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ s) :
    (deningerBigWittLeftPrimeMarginal (deningerBigWittCrossPairFiniteRightLegPacket a s) p).re =
      ∑ q ∈ s.erase p, ((a p).re - (a q).re) := by
  classical
  rw [deningerBigWittLeftPrimeMarginal_coherent, if_pos hp]
  have hsum : (∑ q ∈ s, ((a p).re - (a q).re)) =
      ∑ q ∈ s.erase p, ((a p).re - (a q).re) := by
    rw [← Finset.sum_erase_add _ _ hp]
    simp
  rw [← hsum]
  simp [Finset.sum_sub_distrib, nsmul_eq_mul]

/-- Positivity on both edge orientations restricts every complete coherent repair of a
reciprocal row to removal of at most its unnormalized reciprocal coefficient. -/
theorem coherentPositiveRepair_removed_mass_bound
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) (p : Nat.Primes)
    (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ i, i.1.1 ≠ p → (f i).re = 0)
    (hrow : ∀ q (hpq : p ≠ q), (f ⟨(p,q),hpq⟩).re ≤ K / (q : ℕ))
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    (hpos : ∀ i, 0 ≤ (f i - deningerBigWittCrossPairFiniteRightLegPacket a s i).re) :
    0 ≤ (deningerBigWittLeftPrimeMarginal
      (deningerBigWittCrossPairFiniteRightLegPacket a s) p).re ∧
    (deningerBigWittLeftPrimeMarginal
      (deningerBigWittCrossPairFiniteRightLegPacket a s) p).re ≤ K := by
  classical
  by_cases hp : p ∈ s
  · rw [deningerBigWittLeftPrimeMarginal_coherent_re_sum_erase a s p hp]
    rcases (s.erase p).eq_empty_or_nonempty with hempty | hne
    · simpa [hempty] using hK
    obtain ⟨q,hq,hmax⟩ := Finset.exists_mem_eq_sup (s.erase p) hne (fun q => (q : ℕ))
    have hqs := (Finset.mem_erase.mp hq).2
    have hqp := (Finset.mem_erase.mp hq).1
    let t : ℝ := (a p).re - (a q).re
    have ht0 : 0 ≤ t := by
      have h := hpos ⟨(q,p),hqp⟩
      rw [Complex.sub_re, hf _ hqp, deningerBigWittCrossPairFiniteRightLegPacket_apply,
        if_pos ⟨hqs,hp⟩, deningerBigWittCrossPairRightLeg, Complex.conj_re, Complex.sub_re] at h
      dsimp [t]
      linarith
    have ht : t ≤ K / (q : ℕ) := by
      have h := hpos ⟨(p,q),hqp.symm⟩
      rw [Complex.sub_re, deningerBigWittCrossPairFiniteRightLegPacket_apply,
        if_pos ⟨hp,hqs⟩, deningerBigWittCrossPairRightLeg, Complex.conj_re, Complex.sub_re] at h
      exact (sub_nonneg.mp h).trans (hrow q hqp.symm)
    have heq : (∑ r ∈ s.erase p, ((a p).re - (a r).re)) = (s.erase p).card * t := by
      calc
        _ = ∑ r ∈ s.erase p, t := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [coherentPositiveRepair_profile_re_eq_off_anchor f p hf a s hpos r q
            (Finset.mem_erase.mp hr).2 hqs (Finset.mem_erase.mp hr).1 hqp]
        _ = _ := by simp [nsmul_eq_mul]
    rw [heq]
    have hcard : ((s.erase p).card : ℝ) ≤ (q : ℕ) := by
      exact_mod_cast (hmax ▸ primeFinset_card_le_sup (s.erase p))
    have hq0 : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.2.pos
    refine ⟨mul_nonneg (Nat.cast_nonneg _) ht0, ?_⟩
    calc
      _ ≤ (q : ℕ) * t := mul_le_mul_of_nonneg_right hcard ht0
      _ ≤ (q : ℕ) * (K / (q : ℕ)) := mul_le_mul_of_nonneg_left ht hq0.le
      _ = K := by field_simp
  · simpa [deningerBigWittLeftPrimeMarginal_coherent, hp] using hK


theorem deningerBigWittWoldNormalizedPacket_re_zero_off_left (a n : ℕ)
    (i : DeningerCalderonWittCrossPrimePacketIndex) (hi : i.1.1 ≠ nthPrimeSubtype a) :
    (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n i).re = 0 := by
  classical
  have hnot : i ∉ deningerBigWittWoldFixedLeftRightEdgePrefix a (n + 1) :=
    fun h => hi (deningerBigWittWoldFixedLeftRightEdgePrefix_left h)
  simp [deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket, Finsupp.smul_apply,
    deningerBigWittWoldFixedLeftRightEdgeRawPacket_apply, hnot]

/-- The coefficient budget is determined by the original prime and raw row mass. -/
def deningerBigWittWoldCoherentRemovalBudget (a n : ℕ) : ℝ :=
  (nthPrimeSubtype a : ℝ)⁻¹ * (deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1))⁻¹

theorem deningerBigWittWoldCoherentRemovalBudget_nonneg (a n : ℕ) :
    0 ≤ deningerBigWittWoldCoherentRemovalBudget a n := by
  exact mul_nonneg (inv_nonneg.mpr (nthPrimeSubtype_pos a).le)
    (inv_nonneg.mpr (deningerBigWittWoldFixedLeftRightEdgeMass_pos a n).le)

theorem deningerBigWittWoldNormalizedPacket_re_le_reciprocal (a n : ℕ)
    (q : Nat.Primes) (hq : nthPrimeSubtype a ≠ q) :
    (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n ⟨(nthPrimeSubtype a,q),hq⟩).re ≤
      deningerBigWittWoldCoherentRemovalBudget a n / (q : ℕ) := by
  classical
  rw [deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket, Finsupp.smul_apply, smul_eq_mul,
    deningerBigWittWoldFixedLeftRightEdgeRawPacket_apply]
  split_ifs with hi
  · have hcoeff (i : DeningerCalderonWittCrossPrimePacketIndex) :
        deningerBigWittCrossPrimePacketRawCoefficient i =
          (((i.1.1 : ℕ) : ℝ)⁻¹ * ((i.1.2 : ℕ) : ℝ)⁻¹ : ℝ) := by
      simp [deningerBigWittCrossPrimePacketRawCoefficient, deningerBigWittCrossPrimeAtom,
        deningerBigWittPrimeFace]
    rw [hcoeff]
    have heq :
        (deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1) : ℂ)⁻¹ *
          (((nthPrimeSubtype a : ℝ)⁻¹ * ((q : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) =
        (((deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1))⁻¹ *
          ((nthPrimeSubtype a : ℝ)⁻¹ * ((q : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [heq, Complex.ofReal_re]
    unfold deningerBigWittWoldCoherentRemovalBudget
    rw [div_eq_mul_inv]
    exact le_of_eq (by ring)
  · simpa using div_nonneg (deningerBigWittWoldCoherentRemovalBudget_nonneg a n)
      (show (0 : ℝ) ≤ (q : ℕ) by positivity)

theorem deningerBigWittWoldPositiveRepair_removed_mass_bound (a n : ℕ)
    (b : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    (hpos : ∀ i, 0 ≤ (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n i -
      deningerBigWittCrossPairFiniteRightLegPacket b s i).re) :
    0 ≤ (deningerBigWittLeftPrimeMarginal
      (deningerBigWittCrossPairFiniteRightLegPacket b s) (nthPrimeSubtype a)).re ∧
    (deningerBigWittLeftPrimeMarginal
      (deningerBigWittCrossPairFiniteRightLegPacket b s) (nthPrimeSubtype a)).re ≤
        deningerBigWittWoldCoherentRemovalBudget a n := by
  exact coherentPositiveRepair_removed_mass_bound
    (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n) (nthPrimeSubtype a)
    (deningerBigWittWoldCoherentRemovalBudget a n)
    (deningerBigWittWoldCoherentRemovalBudget_nonneg a n)
    (deningerBigWittWoldNormalizedPacket_re_zero_off_left a n)
    (deningerBigWittWoldNormalizedPacket_re_le_reciprocal a n) b s hpos

theorem tendsto_deningerBigWittWoldCoherentRemovalBudget (a : ℕ) :
    Tendsto (deningerBigWittWoldCoherentRemovalBudget a) atTop (nhds 0) := by
  have hmass : Tendsto
      (fun n => deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1)) atTop atTop :=
    (tendsto_deningerBigWittWoldFixedLeftRightEdgeMass_atTop a).comp
      (Filter.tendsto_add_atTop_nat 1)
  change Tendsto (fun n => (nthPrimeSubtype a : ℝ)⁻¹ *
    (deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1))⁻¹) atTop (nhds 0)
  simpa using hmass.inv_tendsto_atTop.const_mul (nthPrimeSubtype a : ℝ)⁻¹

theorem deningerBigWittWoldPositiveRepair_retained_mass_bound (a n : ℕ)
    (b : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    (hpos : ∀ i, 0 ≤ (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n i -
      deningerBigWittCrossPairFiniteRightLegPacket b s i).re) :
    1 - deningerBigWittWoldCoherentRemovalBudget a n ≤
      (deningerBigWittLeftPrimeMarginal
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
          deningerBigWittCrossPairFiniteRightLegPacket b s) (nthPrimeSubtype a)).re ∧
    (deningerBigWittLeftPrimeMarginal
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
          deningerBigWittCrossPairFiniteRightLegPacket b s) (nthPrimeSubtype a)).re ≤ 1 := by
  rw [deningerBigWittLeftPrimeMarginal_sub,
    deningerBigWittLeftPrimeMarginal_woldFixedLeftRightEdgeNormalizedPacket,
    Finsupp.sub_apply, Finsupp.single_eq_same, Complex.sub_re, Complex.one_re]
  obtain ⟨h₁,h₂⟩ := deningerBigWittWoldPositiveRepair_removed_mass_bound a n b s hpos
  constructor <;> linarith

theorem tendsto_deningerBigWittWoldPositiveRepair_retained_mass (a : ℕ)
    (b : ℕ → Nat.Primes → ℂ) (s : ℕ → Finset Nat.Primes)
    (hpos : ∀ n i, 0 ≤ (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n i -
      deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n) i).re) :
    Tendsto (fun n => (deningerBigWittLeftPrimeMarginal
      (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n)) (nthPrimeSubtype a)).re)
      atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => 1 - deningerBigWittWoldCoherentRemovalBudget a n)
    (h := fun _ => (1 : ℝ))
  · simpa using tendsto_const_nhds.sub (tendsto_deningerBigWittWoldCoherentRemovalBudget a)
  · exact tendsto_const_nhds
  · intro n
    exact (deningerBigWittWoldPositiveRepair_retained_mass_bound a n (b n) (s n) (hpos n)).1
  · intro n
    exact (deningerBigWittWoldPositiveRepair_retained_mass_bound a n (b n) (s n) (hpos n)).2



theorem finitePrimeMarginalEnergy_indicator (p : Nat.Primes) (m : Nat.Primes →₀ ℂ) :
    finitePrimeMarginalEnergy (fun q => if q = p then 1 else 0) m = m p := by
  classical
  have hcast (q : Nat.Primes) : ((if q = p then 1 else 0 : ℝ) : ℂ) =
      if q = p then 1 else 0 := by split_ifs <;> rfl
  simp only [finitePrimeMarginalEnergy, Finsupp.sum, hcast, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq']
  by_cases hp : m p = 0 <;> simp [Finsupp.mem_support_iff, hp]

theorem primeLabelledEnergyReporter_re_anchor_bound (A : ℝ) (hA : 0 ≤ A)
    (p : Nat.Primes) (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ)
    (hf : ∀ i, 0 ≤ (f i).re) :
    (A / (p : ℕ)) * (deningerBigWittLeftPrimeMarginal f p).re ≤
      (primeLabelledEnergyReporter (fun q => A / (q : ℕ)) f).re := by
  classical
  have hm : primeLabelledEnergyReporter (fun q => if q = p then 1 else 0) f =
      deningerBigWittLeftPrimeMarginal f p := by
    rw [primeLabelledEnergyReporter_eq_marginal, finitePrimeMarginalEnergy_indicator]
  rw [← hm, primeLabelledEnergyReporter_re_sum, primeLabelledEnergyReporter_re_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hip : i.1.1 = p
  · simp [hip]
  · simp only [hip, if_false, zero_mul, mul_zero]
    exact mul_nonneg (div_nonneg hA (by positivity)) (hf i)

/-- A positive repaired source retains an explicit lower bound on its original energy. -/
theorem deningerBigWittWoldPositiveRepair_energy_lower (A : ℝ) (hA : 0 ≤ A) (a n : ℕ)
    (b : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    (hpos : ∀ i, 0 ≤ (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n i -
      deningerBigWittCrossPairFiniteRightLegPacket b s i).re) :
    (A / (nthPrimeSubtype a : ℕ)) * (1 - deningerBigWittWoldCoherentRemovalBudget a n) ≤
      (primeLabelledEnergyReporter (fun q => A / (q : ℕ))
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
          deningerBigWittCrossPairFiniteRightLegPacket b s)).re := by
  calc
    _ ≤ (A / (nthPrimeSubtype a : ℕ)) * (deningerBigWittLeftPrimeMarginal
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
          deningerBigWittCrossPairFiniteRightLegPacket b s) (nthPrimeSubtype a)).re :=
      mul_le_mul_of_nonneg_left
        (deningerBigWittWoldPositiveRepair_retained_mass_bound a n b s hpos).1
        (div_nonneg hA (by positivity))
    _ ≤ _ := primeLabelledEnergyReporter_re_anchor_bound A hA (nthPrimeSubtype a) _ hpos

theorem deningerBigWittWoldPositiveRepair_eventually_energy_lower
    (A : ℝ) (hA : 0 ≤ A) (a : ℕ)
    (b : ℕ → Nat.Primes → ℂ) (s : ℕ → Finset Nat.Primes)
    (hpos : ∀ n i, 0 ≤ (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n i -
      deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n) i).re) :
    ∀ᶠ n in atTop, A / (2 * (nthPrimeSubtype a : ℕ)) ≤
      (primeLabelledEnergyReporter (fun q => A / (q : ℕ))
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
          deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n))).re := by
  have hbudget := (tendsto_deningerBigWittWoldCoherentRemovalBudget a).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [hbudget] with n hn
  have hscale : 0 ≤ A / (nthPrimeSubtype a : ℕ) := div_nonneg hA (by positivity)
  calc
    _ = (A / (nthPrimeSubtype a : ℕ)) * (1 / 2) := by ring
    _ ≤ (A / (nthPrimeSubtype a : ℕ)) * (1 - deningerBigWittWoldCoherentRemovalBudget a n) :=
      mul_le_mul_of_nonneg_left (by linarith) hscale
    _ ≤ _ := deningerBigWittWoldPositiveRepair_energy_lower A hA a n (b n) (s n) (hpos n)

/-- No moving complete coherent correction preserving nonnegative real edge coefficients
can make the fixed positive reciprocal energy vanish. -/
theorem deningerBigWittWoldPositiveRepair_not_tendsto_energy_zero
    (A : ℝ) (hA : 0 < A) (a : ℕ)
    (b : ℕ → Nat.Primes → ℂ) (s : ℕ → Finset Nat.Primes)
    (hpos : ∀ n i, 0 ≤ (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n i -
      deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n) i).re) :
    ¬ Tendsto (fun n => primeLabelledEnergyReporter (fun q => A / (q : ℕ))
      (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n))) atTop (nhds 0) := by
  intro hE
  have hEre : Tendsto (fun n => (primeLabelledEnergyReporter (fun q => A / (q : ℕ))
      (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
        deningerBigWittCrossPairFiniteRightLegPacket (b n) (s n))).re) atTop (nhds 0) :=
    Complex.continuous_re.continuousAt.tendsto.comp hE
  have hlimit : Tendsto (fun n => (A / (nthPrimeSubtype a : ℕ)) *
      (1 - deningerBigWittWoldCoherentRemovalBudget a n)) atTop
        (nhds (A / (nthPrimeSubtype a : ℕ))) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    simpa using (hconst.sub (tendsto_deningerBigWittWoldCoherentRemovalBudget a)).const_mul
      (A / (nthPrimeSubtype a : ℕ))
  have hbad := le_of_tendsto_of_tendsto' hlimit hEre
    (fun n => deningerBigWittWoldPositiveRepair_energy_lower A hA.le a n (b n) (s n) (hpos n))
  exact (not_le_of_gt (div_pos hA (nthPrimeSubtype_pos a))) hbad


end
end RHTower.HedenmalmThetaSource
