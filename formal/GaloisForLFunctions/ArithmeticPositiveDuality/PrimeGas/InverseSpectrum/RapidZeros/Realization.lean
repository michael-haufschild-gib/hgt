import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.Limits
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.Overlap
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.BalancedPair
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.Resonance

/-! # All retained occupation laws at prescribed fast zeros -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

private def retainedFraction (j : ℕ) : ℝ := 1-1/((j:ℝ)+2)

private theorem fraction_bounds (j : ℕ) : 0 < retainedFraction j ∧ retainedFraction j < 1 := by
  have hj : 1 < (j:ℝ)+2 := by linarith only [Nat.cast_nonneg (α := ℝ) j]
  have hd := one_div_lt_one_div_of_lt zero_lt_one hj
  have hp : 0 < 1/((j:ℝ)+2) := one_div_pos.mpr (zero_lt_one.trans hj)
  have hl : 1/((j:ℝ)+2) < 1 := by simpa only [div_one] using hd
  unfold retainedFraction
  constructor <;> linarith only [hp,hl]

private theorem fraction_tendsto : Tendsto retainedFraction atTop (𝓝 1) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp (tendsto_add_atTop_nat 2)
  have hz : Tendsto (fun j : ℕ => 1/((j:ℝ)+2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat] using h
  change Tendsto (fun j : ℕ => 1-1/((j:ℝ)+2)) atTop (𝓝 1)
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub hz

private def movedTail (p : Nat.Primes) (a : ℕ+) : ExteriorLaw :=
  insertedExterior a (exteriorLaw (lacunaryOmission p))

/-- The positive translated tail enforces exteriority even for a finite target of mass exactly one half. -/
private def baseLaw (p : Nat.Primes) (m : ℕ+ → ℝ) (hm : halfLaw m) (a : ℕ+) (j : ℕ) : ExteriorLaw := by
  let c := 2*retainedFraction j
  let d := 1-c*(∑' n, m n)
  let ρ := movedTail p a
  let ν := fun n => c*m n+d*ρ.val n
  have hc : 0 < c := mul_pos (by norm_num) (fraction_bounds j).1
  have hd : 0 < d := by
    have h := mul_le_mul_of_nonneg_left (show 2*(∑' n, m n) ≤ 1 by linarith only [hm.2.2]) (fraction_bounds j).1.le
    dsimp only [d,c]
    linarith only [h,(fraction_bounds j).2]
  have hρ : HasSum ρ.val 1 := Equiv.pnatEquivNat.symm.hasSum_iff.mp ρ.property.2.1
  have hn : HasSum ν 1 := by
    have h := (hm.2.1.hasSum.mul_left c).add (hρ.mul_left d)
    have he : c*(∑' n, m n)+d*1 = 1 := by dsimp only [d]; ring
    rw [he] at h
    exact h
  exact ⟨ν,fun n => add_nonneg (mul_nonneg hc.le (hm.1 n)) (mul_nonneg hd.le (ρ.property.1 n)),
    Equiv.pnatEquivNat.symm.hasSum_iff.mpr hn,
    fun h => exterior_mean_of_dominates ρ hd (fun n => le_add_of_nonneg_left (mul_nonneg hc.le (hm.1 n)))
      ((labelMean_summable_iff ν).mpr h)⟩

/-- The unpaired exterior preparation whose retained coordinates tend to twice the target. -/
def recoverySeed (p : Nat.Primes) (m : ℕ+ → ℝ) (hm : halfLaw m) (j : ℕ) :=
  lawOmission (baseLaw p m hm (resonantBlock p j) j)

/-- Canonical rapidly orthogonal preparations for a chosen prime and limiting occupation array. -/
def realizingWave (p : Nat.Primes) (m : ℕ+ → ℝ) (hm : halfLaw m) (j : ℕ) :=
  pairedWave (resonantBlock p j) (recoverySeed p m hm j)

theorem realizingWave_zero (p : Nat.Primes) (m : ℕ+ → ℝ) (hm : halfLaw m) (j : ℕ) :
    compositionResponse (realizingWave p m hm j) (criticalTime (resonantTime p j)) = 0 := by
  rw [realizingWave,paired_response,resonantBlock_phase,add_neg_cancel,zero_mul,zero_div]

/-- Below the inserted block the target coordinates are known exactly, including before taking a limit. -/
theorem realizingWave_below (p : Nat.Primes) (m : ℕ+ → ℝ) (hm : halfLaw m) (j : ℕ) (n : ℕ+)
    (h : (n:ℕ) < (resonantBlock p j).val) :
    occupationProbability (realizingWave p m hm j) n = (1-1/((j:ℝ)+2))*m n := by
  rw [realizingWave,paired_probability,recoverySeed,lawOmission_probability,insertedMass_below _ _ _ h,add_zero]
  change (2*retainedFraction j*m n+_ * insertedMass (resonantBlock p j) _ n)/2 = _
  rw [insertedMass_below _ _ _ h,mul_zero,add_zero]
  unfold retainedFraction
  ring

theorem realizingWave_limit (p : Nat.Primes) (m : ℕ+ → ℝ) (hm : halfLaw m) (n : ℕ+) :
    Tendsto (fun j => occupationProbability (realizingWave p m hm j) n) atTop (𝓝 (m n)) := by
  have ht : Tendsto (fun j => retainedFraction j*m n) atTop (𝓝 (m n)) := by
    simpa only [one_mul] using fraction_tendsto.mul_const (m n)
  apply ht.congr'
  filter_upwards [resonantBlock_escapes p n] with j hj
  exact (realizingWave_below p m hm j n hj).symm

/-- With any specified elementary clock the retained laws are exactly the subprobabilities of mass at most one half. -/
theorem prescribed_fast_zeros_iff (p : Nat.Primes) (m : ℕ+ → ℝ) :
    (∃ v : ℕ → MissingWave, (∀ j, compositionResponse (v j) (criticalTime (resonantTime p j)) = 0) ∧
      ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) ↔ halfLaw m :=
  ⟨fun ⟨_,hz,hm⟩ => fast_zero_limit_halfLaw (resonantTime_tendsto p) hz hm,
    fun hm => ⟨realizingWave p m hm,realizingWave_zero p m hm,realizingWave_limit p m hm⟩⟩

/-- Allowing arbitrary positive orthogonality times tending to zero produces the same class of limits. -/
theorem fast_zero_spectra_iff (m : ℕ+ → ℝ) :
    (∃ (t : ℕ → ℝ) (v : ℕ → MissingWave), (∀ j, 0 < t j) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ j, compositionResponse (v j) (criticalTime (t j)) = 0) ∧
      ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) ↔ halfLaw m := by
  refine ⟨fun ⟨_,_,_,ht,hz,hm⟩ => fast_zero_limit_halfLaw ht hz hm,fun hm => ?_⟩
  let p : Nat.Primes := ⟨2,Nat.prime_two⟩
  exact ⟨resonantTime p,realizingWave p m hm,resonantTime_pos p,resonantTime_tendsto p,
    realizingWave_zero p m hm,realizingWave_limit p m hm⟩

/-- No probability outside the occupations of one elementary species. -/
def raySupportedLaw (p : Nat.Primes) (m : ℕ+ → ℝ) := ∀ n ∉ Set.range (primeRayLabel p), m n = 0

theorem raySupportedLaw_iff (p : Nat.Primes) (v : MissingWave) :
    raySupportedLaw p (occupationProbability v) ↔ onPrimeRay p v.val := by
  have hM : ‖v.val‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v))
  constructor
  · intro h n hn
    have he := h n hn
    rw [occupationProbability,div_eq_zero_iff] at he
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (he.resolve_right hM))
  · intro h n hn
    simp only [occupationProbability,h n hn,norm_zero,zero_pow two_ne_zero,zero_div]

/-- Inserting powers of the same prime preserves support on its occupation ray. -/
theorem insertedMass_onPrimeRay {p : Nat.Primes} {m : ℕ+ → ℝ} (h : raySupportedLaw p m) (k : ℕ) :
    raySupportedLaw p (insertedMass (primeRayLabel p k) m) := by
  intro n hn
  by_cases he : n ∈ Set.range (fun x : ℕ+ => primeRayLabel p k*x)
  · obtain ⟨x,rfl⟩ := he
    rw [insertedMass_at]
    apply h
    rintro ⟨l,rfl⟩
    exact hn ⟨k+l,pow_add _ _ _⟩
  · exact insertedMass_off _ _ _ he

theorem realizingWave_onPrimeRay (p : Nat.Primes) (m : ℕ+ → ℝ) (hm : halfLaw m)
    (h : raySupportedLaw p m) (j : ℕ) : onPrimeRay p (realizingWave p m hm j).val := by
  let a := resonantBlock p j
  let ν := baseLaw p m hm a j
  have hρ : raySupportedLaw p (movedTail p a).val :=
    insertedMass_onPrimeRay ((raySupportedLaw_iff p _).mpr (lacunary_prime_support p)) (j+1)
  have hν : raySupportedLaw p ν.val := by
    intro n hn
    change 2*retainedFraction j*m n+_*(movedTail p a).val n = 0
    rw [h n hn,hρ n hn,mul_zero,mul_zero,zero_add]
  apply (raySupportedLaw_iff p _).mp
  intro n hn
  rw [realizingWave,paired_probability,recoverySeed,lawOmission_probability]
  change (ν.val n+insertedMass a ν.val n)/2 = 0
  have ha : insertedMass a ν.val n = 0 := (insertedMass_onPrimeRay hν (j+1)) n hn
  rw [hν n hn,ha,zero_add,zero_div]

/-- Restricting all preparations to one species restricts the retained array only by support on its powers. -/
theorem one_prime_fast_zeros_iff (p : Nat.Primes) (m : ℕ+ → ℝ) :
    (∃ v : ℕ → MissingWave, (∀ j, onPrimeRay p (v j).val) ∧
      (∀ j, compositionResponse (v j) (criticalTime (resonantTime p j)) = 0) ∧
      ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) ↔
      halfLaw m ∧ raySupportedLaw p m := by
  constructor
  · rintro ⟨v,hr,hz,hm⟩
    refine ⟨(prescribed_fast_zeros_iff p m).mp ⟨v,hz,hm⟩,fun n hn => ?_⟩
    have h : (fun j => occupationProbability (v j) n) =ᶠ[atTop] fun _ => 0 :=
      Eventually.of_forall (fun j => (raySupportedLaw_iff p _).mpr (hr j) n hn)
    exact tendsto_nhds_unique (hm n) h.tendsto
  · rintro ⟨hm,hr⟩
    exact ⟨realizingWave p m hm,realizingWave_onPrimeRay p m hm hr,realizingWave_zero p m hm,realizingWave_limit p m hm⟩

/-- Complete classification using only Hilbert-space orthogonality of the outgoing split pairs as the zero test. -/
theorem orthogonal_split_limits_iff (p : Nat.Primes) (m : ℕ+ → ℝ) :
    (∃ v : ℕ → MissingWave,
      (∀ j, inner ℂ (clockSplit (-(resonantTime p j)) (v j).val) (clockSplit (resonantTime p j) (v j).val) = 0) ∧
      ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n))) ↔ halfLaw m := by
  simpa only [split_pair_orthogonal_iff] using prescribed_fast_zeros_iff p m

/-- Half of the probability can remain at the vacuum alone, with all escaping probability carried by powers of the chosen prime. -/
theorem sharp_vacuum_retention (p : Nat.Primes) :
    ∃ v : ℕ → MissingWave, (∀ j, onPrimeRay p (v j).val) ∧
      (∀ j, inner ℂ (clockSplit (-(resonantTime p j)) (v j).val) (clockSplit (resonantTime p j) (v j).val) = 0) ∧
      ∀ F : Finset ℕ+, 1 ∈ F → Tendsto (fun j => windowMass (v j) F) atTop (𝓝 (1/2)) := by
  let m := fun n : ℕ+ => if n = 1 then (1/2:ℝ) else 0
  have hs : HasSum m (1/2) := hasSum_ite_eq (1:ℕ+) (1/2:ℝ)
  have hp (n : ℕ+) : 0 ≤ m n := by dsimp only [m]; split <;> norm_num
  have hm : halfLaw m := ⟨hp,hs.summable,hs.tsum_eq.le⟩
  have hr : raySupportedLaw p m := by
    intro n hn
    have h : n ≠ 1 := fun he => hn ⟨0,(show primeRayLabel p 0 = 1 from pow_zero _).trans he.symm⟩
    exact if_neg h
  obtain ⟨v,hv,hz,hl⟩ := (one_prime_fast_zeros_iff p m).mpr ⟨hm,hr⟩
  refine ⟨v,hv,fun j => (split_pair_orthogonal_iff _ _).mpr (hz j),fun F hF => ?_⟩
  have hlim := tendsto_finsetSum F (fun n _ => hl n)
  have hval : ∑ n ∈ F, m n = 1/2 := by simp [m,hF]
  rw [hval] at hlim
  exact hlim

/-- Each retained coordinate of the seed is twice that of its balanced realization once the block has passed it. -/
theorem recoverySeed_below (p : Nat.Primes) (m : ℕ+ → ℝ) (hm : halfLaw m) (j : ℕ) (n : ℕ+)
    (hn : (n:ℕ) < (resonantBlock p j).val) :
    occupationProbability (recoverySeed p m hm j) n = 2*((1-1/((j:ℝ)+2))*m n) := by
  have h := realizingWave_below p m hm j n hn
  rw [realizingWave,paired_probability,insertedMass_below _ _ _ hn,add_zero] at h
  linarith only [h]

theorem recoverySeed_limit (p : Nat.Primes) (m : ℕ+ → ℝ) (hm : halfLaw m) (n : ℕ+) :
    Tendsto (fun j => occupationProbability (recoverySeed p m hm j) n) atTop (𝓝 (2*m n)) := by
  apply ((realizingWave_limit p m hm n).const_mul 2).congr'
  filter_upwards [resonantBlock_escapes p n] with j hj
  rw [realizingWave_below p m hm j n hj,recoverySeed_below p m hm j n hj]

theorem recoverySeed_support (p : Nat.Primes) (m : ℕ+ → ℝ) (hm : halfLaw m)
    (hr : raySupportedLaw p m) (j : ℕ) : raySupportedLaw p (occupationProbability (recoverySeed p m hm j)) := by
  intro n hn
  have h := ((raySupportedLaw_iff p _).mpr (realizingWave_onPrimeRay p m hm hr j)) n hn
  rw [realizingWave,paired_probability] at h
  have hi := insertedMass_nonneg (resonantBlock p j) (occupationLaw_nonneg (recoverySeed p m hm j)) n
  exact le_antisymm (by linarith only [h,hi]) (occupationLaw_nonneg _ _)

#print axioms insertedMass_onPrimeRay
#print axioms recoverySeed_below
#print axioms recoverySeed_limit
#print axioms recoverySeed_support

#print axioms sharp_vacuum_retention
#print axioms orthogonal_split_limits_iff
#print axioms raySupportedLaw_iff
#print axioms realizingWave_onPrimeRay
#print axioms one_prime_fast_zeros_iff
#print axioms realizingWave_zero
#print axioms realizingWave_below
#print axioms realizingWave_limit
#print axioms prescribed_fast_zeros_iff
#print axioms fast_zero_spectra_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
