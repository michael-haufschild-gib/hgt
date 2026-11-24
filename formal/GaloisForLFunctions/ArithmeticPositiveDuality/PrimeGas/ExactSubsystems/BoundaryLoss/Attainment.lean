import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BoundaryLoss.PhaseEquality
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BoundaryLoss.Sharpness
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.LacunaryLaw
import GaloisForLFunctions.RHTower.PrimeLogIncommensuratePhaseClock

/-! # Finite attainment of the Euler bound is equivalent to a common prime phase period -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing
open _root_.RHTower.PrimeCoShift

/-- All selected prime clocks return to the phase of the vacuum after the same positive number of steps. -/
def commonPhasePeriod (P : Finset Nat.Primes) (s : ℂ) (d : ℕ+) : Prop :=
  ∀ p ∈ P, (heat s (primePNat p))^d.val = (heat (s.re:ℂ) (primePNat p))^d.val

private theorem primePower_mem_window (P : Finset Nat.Primes) {p : Nat.Primes} (hp : p ∈ P) (k : ℕ) :
    (primeRayLabel p k).val ∈ Nat.factoredNumbers (primeWindow P) := by
  have h1 : 1 ∈ Nat.factoredNumbers (primeWindow P) := Nat.mem_factoredNumbers.mpr ⟨one_ne_zero,by simp⟩
  have hmem : p.val ∈ Nat.factoredNumbers (primeWindow P) := by
    apply Nat.mem_factoredNumbers_of_primeFactors_subset p.property.ne_zero
    rw [p.property.primeFactors]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_map.mpr ⟨p,hp,rfl⟩)
  change p.val^k ∈ _
  induction k with
  | zero => simpa only [pow_zero] using h1
  | succ k ih => rw [pow_succ]; exact Nat.mul_mem_factoredNumbers ih hmem

/-- No bounded factor can absorb every positive pure power of any prime. -/
theorem complement_contains_prime_power {ι κ : Type*} [Fintype ι] {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (p : Nat.Primes) : ∃ (k : ℕ+) (j : κ), b j = primeRayLabel p k.val := by
  let M := Finset.univ.sup (fun i => (a i).val)
  have hm : M < p.val^M := Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left p.property.two_le M)
  obtain ⟨⟨i,j⟩,hj⟩ := h.2 (primeRayLabel p M)
  have he : (a i).val*(b j).val = p.val^M := congrArg PNat.val hj
  obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow p.property).mp (Dvd.intro_left _ he)
  have hk0 : 0 < k := by
    by_contra! hn
    have h1 : (b j).val = 1 := by simpa only [Nat.eq_zero_of_le_zero hn,pow_zero] using hk
    rw [h1,mul_one] at he
    exact (not_le_of_gt hm) (he ▸ (Finset.le_sup (f := fun x => (a x).val) (Finset.mem_univ i)))
  exact ⟨⟨k,hk0⟩,j,PNat.coe_injective hk⟩

private theorem period_of_attainment {ι κ : Type*} [Fintype ι] (P : Finset Nat.Primes)
    {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b)
    (ha : ∀ i, (a i).val ∈ Nat.factoredNumbers (primeWindow P)) {s : ℂ} (hs : 0 < s.re)
    (he : traceVisibility a s = eulerEnvelope P s) : ∃ d, commonPhasePeriod P s d := by
  classical
  have halign := (visibility_eq_iff_complement P h ha hs).mp he
  choose k j hj using complement_contains_prime_power h
  let d := ∏ p ∈ P, (k p).val
  refine ⟨⟨d,Finset.prod_pos (fun p _ => (k p).pos)⟩,?_⟩
  intro p hp
  have hw : (b (j p)).val ∈ Nat.factoredNumbers (primeWindow P) := hj p ▸ primePower_mem_window P hp _
  have hv := halign ⟨j p,hw⟩
  change heat s (b (j p)) = heat (s.re:ℂ) (b (j p)) at hv
  rw [hj,heat_primeRayLabel,heat_primeRayLabel] at hv
  obtain ⟨l,hl⟩ := Finset.dvd_prod_of_mem (fun q => (k q).val) hp
  change (heat s (primePNat p))^d = (heat (s.re:ℂ) (primePNat p))^d
  rw [show d = _ from hl,pow_mul,pow_mul,hv]

private theorem box_clear (P : Finset Nat.Primes) (d : ℕ+) (s : ℂ) :
    finiteHeatTrace (boxLabel P d) s * (∏ p ∈ P, (heat s (primePNat p)-1)) =
      ∏ p ∈ P, ((heat s (primePNat p))^d.val-1) := by
  rw [box_trace,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [Fin.sum_univ_eq_sum_range]
  exact geom_sum_mul _ _

/-- The box of one common radix already realizes the infimum exactly. -/
theorem box_attains_of_common_period (P : Finset Nat.Primes) {d : ℕ+} {s : ℂ} (hs : 0 < s.re)
    (hd : commonPhasePeriod P s d) : traceVisibility (boxLabel P d) s = eulerEnvelope P s := by
  let D (z : ℂ) := ∏ p ∈ P, (heat z (primePNat p)-1)
  have hD : ∀ {z : ℂ}, 0 < z.re → D z ≠ 0 := by
    intro z hz
    apply Finset.prod_ne_zero_iff.mpr
    intro p _ he
    have hn := prime_heat_lt_one hz p
    rw [sub_eq_zero.mp he,norm_one] at hn
    exact lt_irrefl _ hn
  have he : finiteHeatTrace (boxLabel P d) s * D s = finiteHeatTrace (boxLabel P d) (s.re:ℂ) * D (s.re:ℂ) := by
    rw [show finiteHeatTrace (boxLabel P d) s * D s = _ from box_clear P d s,
      show finiteHeatTrace (boxLabel P d) (s.re:ℂ) * D (s.re:ℂ) = _ from box_clear P d (s.re:ℂ)]
    exact Finset.prod_congr rfl (fun p hp => congrArg (·-1) (hd p hp))
  have hnorm := congrArg norm he
  rw [norm_mul,norm_mul] at hnorm
  have heul : eulerEnvelope P s = ‖D (s.re:ℂ)‖/‖D s‖ := by
    simp only [eulerEnvelope,D,norm_prod,Finset.prod_div_distrib]
    congr 1 <;> apply Finset.prod_congr rfl <;> intro p _ <;> exact norm_sub_rev _ _
  rw [traceVisibility,heul]
  apply (div_eq_div_iff (norm_ne_zero_iff.mpr (finiteSubsystem_zero_free (box_exact P d) (s := (s.re:ℂ)) hs))
    (norm_ne_zero_iff.mpr (hD hs))).mpr
  exact hnorm.trans (mul_comm _ _)

/-- A finite factor achieves the sharp lower visibility exactly when every prime in its allowed window has a common return. -/
theorem envelope_attained_iff (P : Finset Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    eulerEnvelope P s ∈ attainedVisibilities P s ↔ ∃ d, commonPhasePeriod P s d := by
  constructor
  · rintro ⟨A,B,h,ha,he⟩
    exact period_of_attainment P h ha hs he.symm
  · rintro ⟨d,hd⟩
    rw [← box_attains_of_common_period P hs hd]
    exact visibility_mem P (box_exact P d) (box_supported P d) s

private theorem clock_of_period {p : Nat.Primes} {s : ℂ} {d : ℕ+}
    (h : (heat s (primePNat p))^d.val = (heat (s.re:ℂ) (primePNat p))^d.val) :
    _root_.HTGeometry.phaseClockValue (Real.log p.val) (-(d.val:ℝ)*s.im) = 1 := by
  let n := primePNat p
  have he : s = (s.re:ℂ) + (s.im:ℂ)*Complex.I := s.re_add_im.symm
  have hp : (heat ((s.im:ℂ)*Complex.I) n)^d.val = 1 := by
    /- Separate attenuation from the unitary prime clock. -/
    have hs' : heat s n = heat (s.re:ℂ) n * heat ((s.im:ℂ)*Complex.I) n := by
      calc
        _ = heat ((s.re:ℂ)+(s.im:ℂ)*Complex.I) n := congrArg (fun w => heat w n) he
        _ = _ := heat_add _ _ _
    change (heat s n)^d.val = (heat (s.re:ℂ) n)^d.val at h
    rw [hs',mul_pow] at h
    exact mul_left_cancel₀ (pow_ne_zero _ (Complex.exp_ne_zero _)) (h.trans (mul_one _).symm)
  rw [heat,← Complex.exp_nat_mul] at hp
  apply Eq.trans _ hp
  apply congrArg Complex.exp
  change ((Real.log p.val * (-(d.val:ℝ)*s.im) : ℝ):ℂ)*Complex.I =
    (d.val:ℂ)*(-((s.im:ℂ)*Complex.I)*(Real.log p.val:ℂ))
  push_cast
  ring

/-- For two or more prime species the sharp visibility is attained at finite size only at real temperature. -/
theorem multiprime_attainment_iff_real (P : Finset Nat.Primes) {p q : Nat.Primes}
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) {s : ℂ} (hs : 0 < s.re) :
    eulerEnvelope P s ∈ attainedVisibilities P s ↔ s.im = 0 := by
  rw [envelope_attained_iff P hs]
  constructor
  · rintro ⟨d,hd⟩
    have hphase : _root_.RHTower.primeLogPhaseClockPair p.val q.val (-(d.val:ℝ)*s.im) =
        _root_.RHTower.primeLogPhaseClockPair p.val q.val 0 := by
      apply Prod.ext
      · exact (clock_of_period (hd p hp)).trans (by simp [_root_.RHTower.primeLogPhaseClockPair,
          _root_.HTGeometry.phaseClockPair,_root_.HTGeometry.phaseClockValue])
      · exact (clock_of_period (hd q hq)).trans (by simp [_root_.RHTower.primeLogPhaseClockPair,
          _root_.HTGeometry.phaseClockPair,_root_.HTGeometry.phaseClockValue])
    have ht := _root_.RHTower.primeLogPhaseClockPair_injective p.property q.property
      (fun h => hpq (Subtype.ext h)) hphase
    exact (mul_eq_zero.mp ht).resolve_left (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr d.ne_zero))
  · intro hz
    refine ⟨1,fun p _ => ?_⟩
    exact congrArg (fun w => (heat w (primePNat p))^(1:ℕ+).val) (show s = (s.re:ℂ) from Complex.ext rfl hz)

#print axioms multiprime_attainment_iff_real
#print axioms complement_contains_prime_power
#print axioms box_attains_of_common_period
#print axioms envelope_attained_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
