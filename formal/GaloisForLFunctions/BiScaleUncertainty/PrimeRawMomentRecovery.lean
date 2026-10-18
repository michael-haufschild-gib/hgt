import GaloisForLFunctions.BiScaleUncertainty.PrimeRawMomentContrasts

/-!
# Recovery and noise bounds from literal sixth-moment observations

Even CRT lags isolate prime coefficients. Three differences form one residue
indicator; two triples give an exact signed pair product. The resulting fixed
protocol uses at most `64 M^2` literal observations and recovers every actual
prime-family coefficient vector up to common sign, including unknown zeros.
The squared raw-data norm controls all three cubed-Gram stability estimates.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.PrimeRaw
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
open GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem prime_three_le (N : ℕ) (p : oddPrimeModes N) : 3 ≤ (p : ℕ) := by
  have hp := mem_oddPrimeModes.mp p.property
  have hp2 := hp.1.two_le
  obtain ⟨k,hk⟩ := hp.2.1
  omega

/-- Three row differences isolate the zero residue at every admissible odd prime. -/
theorem residue_triple (N : ℕ) (p : oddPrimeModes N) (x : ZMod (p : ℕ)) :
    (residueRow p x-residueRow p (x+1))^2 *
      (residueRow p x-residueRow p (x+2)) =
      if x = 0 then (p : ℝ)^3 else 0 := by
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨(mem_oddPrimeModes.mp p.property).1⟩
  have h1 : (1 : ZMod (p : ℕ)) ≠ 0 := one_ne_zero
  have h2 : (2 : ZMod (p : ℕ)) ≠ 0 := by
    intro h
    have hd : (p : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (p : ℕ)).mp h
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    have := prime_three_le N p
    omega
  by_cases hx : x = 0
  · subst x
    simp [residueRow, h1, h2]
    ring
  · by_cases hx1 : x+1 = 0
    · have hx2 : x+2 ≠ 0 := by
        intro hx2
        apply h1
        linear_combination hx2-hx1
      simp [residueRow, hx, hx1, hx2]
    · simp [residueRow, hx, hx1]

private theorem raw_modes_coprime (N : ℕ) :
    Pairwise (fun p q : oddPrimeModes N => Nat.Coprime (p : ℕ) (q : ℕ)) := by
  intro p q hpq
  apply (Nat.coprime_primes (mem_oddPrimeModes.mp p.property).1
    (mem_oddPrimeModes.mp q.property).1).mpr
  intro h
  exact hpq (Subtype.ext h)

/-- Exact factorization of actual factorial-period averages into prime-coordinate means. -/
theorem prime_product_average (N : ℕ) (F : ∀ p : oddPrimeModes N, ZMod (p : ℕ) → ℝ) :
    (∑ n ∈ Finset.range N.factorial, ∏ p : oddPrimeModes N, F p (n : ZMod (p : ℕ))) /
      (N.factorial : ℝ) = ∏ p : oddPrimeModes N, (∑ x, F p x)/(p : ℝ) := by
  rw [period_average_crt (fun p : oddPrimeModes N => (p : ℕ)) (raw_modes_coprime N)
    N.factorial (Nat.factorial_pos N) (primeFamilyPeriod_dvd_factorial N)
    (fun x => ∏ p, F p (x p))]
  rw [← Fintype.prod_sum]
  simp only [Nat.cast_prod, Finset.prod_div_distrib]

/-- The density of any finite set of zero residue constraints is the product of reciprocal primes. -/
theorem indicator_product_average (N : ℕ) (s : Finset (oddPrimeModes N)) :
    (∑ n ∈ Finset.range N.factorial,
      ∏ p ∈ s, if (n : ZMod (p : ℕ)) = 0 then (1 : ℝ) else 0)/(N.factorial : ℝ) =
      ∏ p ∈ s, 1/(p : ℝ) := by
  have h := prime_product_average N
    (fun p x => if p ∈ s then (if x = 0 then (1 : ℝ) else 0) else 1)
  have hf (p : oddPrimeModes N) :
      (∑ x : ZMod (p : ℕ), if p ∈ s then (if x = 0 then (1 : ℝ) else 0) else 1) /
        (p : ℝ) = if p ∈ s then 1/(p : ℝ) else 1 := by
    have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_oddPrimeModes.mp p.property).1.ne_zero
    by_cases hs : p ∈ s <;> simp [hs, hp, ZMod.card]
  simp_rw [Fintype.prod_ite_mem, hf] at h
  simpa only [Fintype.prod_ite_mem] using h

/-- Six explicit natural lags for one signed coefficient-pair readout. -/
def pairLags (N : ℕ) (p q : oddPrimeModes N) : Fin 6 → ℕ :=
  ![selectiveLag N p, selectiveLag N p, 2*selectiveLag N p,
    selectiveLag N q, selectiveLag N q, 2*selectiveLag N q]

/-- The actual six-difference signal product is a pair of residue indicators. -/
theorem pair_difference_product (N : ℕ) (a : ℕ → ℝ) (p q : oddPrimeModes N) (n : ℕ) :
    (∏ i : Fin 6, (sieveSeq N (primeFamilyWeight N a) n-
      sieveSeq N (primeFamilyWeight N a) (n+pairLags N p q i))) =
      (p : ℝ)^3*(q : ℝ)^3*(a p*a q)^3 *
        (if (n : ZMod (p : ℕ)) = 0 then (1 : ℝ) else 0) *
        (if (n : ZMod (q : ℕ)) = 0 then (1 : ℝ) else 0) := by
  have hd (r : oddPrimeModes N) (j : ℕ) := selective_difference N a r n j
  have hp := residue_triple N p (n : ZMod (p : ℕ))
  have hq := residue_triple N q (n : ZMod (q : ℕ))
  rw [Fin.prod_univ_six]
  change
    (sieveSeq N (primeFamilyWeight N a) n-sieveSeq N (primeFamilyWeight N a) (n+selectiveLag N p))*
    (sieveSeq N (primeFamilyWeight N a) n-sieveSeq N (primeFamilyWeight N a) (n+selectiveLag N p))*
    (sieveSeq N (primeFamilyWeight N a) n-sieveSeq N (primeFamilyWeight N a) (n+2*selectiveLag N p))*
    (sieveSeq N (primeFamilyWeight N a) n-sieveSeq N (primeFamilyWeight N a) (n+selectiveLag N q))*
    (sieveSeq N (primeFamilyWeight N a) n-sieveSeq N (primeFamilyWeight N a) (n+selectiveLag N q))*
    (sieveSeq N (primeFamilyWeight N a) n-sieveSeq N (primeFamilyWeight N a) (n+2*selectiveLag N q)) = _
  have hp1 := hd p 1
  have hq1 := hd q 1
  simp only [one_mul, Nat.cast_one] at hp1 hq1
  rw [hp1, hq1, hd p 2, hd q 2]
  have hpar : parityFactor n ^ 6 = 1 := by
    unfold parityFactor
    split_ifs <;> norm_num
  calc
    _ = parityFactor n^6*(a p*a q)^3*
        ((residueRow p (n : ZMod (p : ℕ))-residueRow p ((n : ZMod (p : ℕ))+1))^2*
          (residueRow p (n : ZMod (p : ℕ))-residueRow p ((n : ZMod (p : ℕ))+2)))*
        ((residueRow q (n : ZMod (q : ℕ))-residueRow q ((n : ZMod (q : ℕ))+1))^2*
          (residueRow q (n : ZMod (q : ℕ))-residueRow q ((n : ZMod (q : ℕ))+2))) := by
      push_cast
      ring
    _ = _ := by
      rw [hpar, hp, hq]
      split_ifs <;> ring

/-- The exact contrast normalizer, including the repeated-prime diagonal. -/
def pairScale (N : ℕ) (p q : oddPrimeModes N) : ℝ :=
  if p = q then (p : ℝ)^5 else (p : ℝ)^2*(q : ℝ)^2

/-- Every contrast normalizer is bounded below uniformly in the cutoff. -/
theorem pairScale_lower (N : ℕ) (p q : oddPrimeModes N) : 81 ≤ pairScale N p q := by
  have hp : (3 : ℝ) ≤ p := by exact_mod_cast prime_three_le N p
  have hq : (3 : ℝ) ≤ q := by exact_mod_cast prime_three_le N q
  unfold pairScale
  split_ifs
  · calc
      (81 : ℝ) ≤ 3^5 := by norm_num
      _ ≤ _ := by gcongr
  · calc
      (81 : ℝ) = 3^2*3^2 := by norm_num
      _ ≤ _ := by gcongr

/-- A signed sum of the 64 literal sixth-moment observations for a prime pair. -/
def pairContrast (N : ℕ) (a : ℕ → ℝ) (p q : oddPrimeModes N) : ℝ :=
  momentContrast N (primeFamilyWeight N a) (pairLags N p q)

/-- The literal observation contrast equals its normalizer times the cubed coefficient product. -/
theorem pairContrast_eq (N : ℕ) (a : ℕ → ℝ) (p q : oddPrimeModes N) :
    pairContrast N a p q = pairScale N p q*(a p*a q)^3 := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (mem_oddPrimeModes.mp p.property).1.ne_zero
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (mem_oddPrimeModes.mp q.property).1.ne_zero
  have hi (n : ℕ) :
      (if (n : ZMod (p : ℕ)) = 0 then (1 : ℝ) else 0) *
        (if (n : ZMod (q : ℕ)) = 0 then (1 : ℝ) else 0) =
      ∏ r ∈ ({p,q} : Finset (oddPrimeModes N)),
        if (n : ZMod (r : ℕ)) = 0 then (1 : ℝ) else 0 := by
    by_cases hpq : p = q
    · subst q
      simp only [Finset.insert_eq_of_mem, Finset.mem_singleton, Finset.prod_singleton]
      split_ifs <;> norm_num
    · simp [hpq]
  unfold pairContrast
  rw [momentContrast_eq]
  simp_rw [pair_difference_product, mul_assoc, hi]
  simp_rw [← Finset.mul_sum, mul_div_assoc]
  rw [indicator_product_average]
  by_cases hpq : p = q
  · subst q
    simp [pairScale]
    field_simp
  · simp [pairScale, hpq]
    field_simp

/-- Normalize the raw contrast to the cubed coefficient Gram matrix. -/
def normalizedReadout (N : ℕ) (a : ℕ → ℝ) (p q : oddPrimeModes N) : ℝ :=
  pairContrast N a p q / pairScale N p q

/-- Exact coefficient identity for the normalized raw readout. -/
theorem normalizedReadout_eq (N : ℕ) (a : ℕ → ℝ) (p q : oddPrimeModes N) :
    normalizedReadout N a p q = (a p*a q)^3 := by
  have hs : pairScale N p q ≠ 0 := by have := pairScale_lower N p q; linarith
  rw [normalizedReadout, pairContrast_eq]
  field_simp

/-- The raw contrast matrix has exactly the common-sign ambiguity, including zero coordinates. -/
theorem normalizedReadouts_iff_common_sign (N : ℕ) (a b : ℕ → ℝ) :
    (∀ p q : oddPrimeModes N, normalizedReadout N a p q = normalizedReadout N b p q) ↔
      (∀ p : oddPrimeModes N, a p = b p) ∨ (∀ p : oddPrimeModes N, a p = -b p) := by
  rw [← primeFamily_readouts_iff_common_sign]
  have hP : (N.factorial : ℝ)^6 ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast Nat.factorial_ne_zero N
  constructor <;> intro h p q
  · have hh := h p q
    rw [normalizedReadout_eq, normalizedReadout_eq] at hh
    rw [primeFamily_sixth_readout, primeFamily_sixth_readout, hh]
  · have hh := h p q
    rw [primeFamily_sixth_readout, primeFamily_sixth_readout] at hh
    rw [normalizedReadout_eq, normalizedReadout_eq]
    exact mul_left_cancel₀ hP hh

/-- One literal sixth translated moment in the finite recovery protocol. -/
def rawObservation (N : ℕ) (a : ℕ → ℝ) (p q : oddPrimeModes N) (b : Fin 6 → Fin 2) : ℝ :=
  translatedMoment N (primeFamilyWeight N a) (cubeLag (pairLags N p q) b)

/-- The finite raw observations recover precisely the common-sign class of the actual family. -/
theorem rawObservations_iff_common_sign (N : ℕ) (a b : ℕ → ℝ) :
    (∀ (p q : oddPrimeModes N) (v : Fin 6 → Fin 2),
      rawObservation N a p q v = rawObservation N b p q v) ↔
      (∀ p : oddPrimeModes N, a p = b p) ∨ (∀ p : oddPrimeModes N, a p = -b p) := by
  constructor
  · intro h
    apply (normalizedReadouts_iff_common_sign N a b).mp
    intro p q
    unfold normalizedReadout pairContrast momentContrast
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    rw [show translatedMoment N (primeFamilyWeight N a) (cubeLag (pairLags N p q) v) =
      translatedMoment N (primeFamilyWeight N b) (cubeLag (pairLags N p q) v) from h p q v]
  · intro h p q v
    exact (primeFamily_sixth_iff_common_sign N a b).mpr h (cubeLag (pairLags N p q) v)

/-- The indexed protocol uses 64 times the square of the number of available modes; repeated lags may be shared. -/
theorem raw_observation_count (N : ℕ) :
    Fintype.card (oddPrimeModes N × oddPrimeModes N × (Fin 6 → Fin 2)) =
      64*Fintype.card (oddPrimeModes N)^2 := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  ring


/-- Finite-difference amplification in squared Euclidean raw-observation norm. -/
theorem momentContrast_error_sq (N : ℕ) (c e : ℕ → ℝ) {m : ℕ} (t : Fin m → ℕ) :
    (momentContrast N c t-momentContrast N e t)^2 ≤
      (2 : ℝ)^m*∑ v : Fin m → Fin 2,
        (translatedMoment N c (cubeLag t v)-translatedMoment N e (cubeLag t v))^2 := by
  let d := fun v : Fin m → Fin 2 =>
    translatedMoment N c (cubeLag t v)-translatedMoment N e (cubeLag t v)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin m → Fin 2 => (1 : ℝ)) (fun v => |d v|)
  have hc' : (∑ v, |d v|)^2 ≤ (2 : ℝ)^m*∑ v, (d v)^2 := by
    simpa [sq_abs] using hc
  have he := momentContrast_error N c e t
  change |momentContrast N c t-momentContrast N e t| ≤ ∑ v, |d v| at he
  have hn : 0 ≤ ∑ v, |d v| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hp := mul_nonneg (sub_nonneg.mpr he)
    (add_nonneg hn (abs_nonneg (momentContrast N c t-momentContrast N e t)))
  have hs := sq_abs (momentContrast N c t-momentContrast N e t)
  dsimp [d] at hc'
  nlinarith

/-- Squared raw-observation discrepancy, counting the stated indexed protocol. -/
def rawNoise (N : ℕ) (a b : ℕ → ℝ) : ℝ :=
  ∑ p : oddPrimeModes N, ∑ q : oddPrimeModes N, ∑ v : Fin 6 → Fin 2,
    (rawObservation N a p q v-rawObservation N b p q v)^2

/-- Uniform noise amplification for each normalized pair readout. -/
theorem normalized_error_sq (N : ℕ) (a b : ℕ → ℝ) (p q : oddPrimeModes N) :
    6561*(normalizedReadout N a p q-normalizedReadout N b p q)^2 ≤
      64*∑ v : Fin 6 → Fin 2, (rawObservation N a p q v-rawObservation N b p q v)^2 := by
  have hc := momentContrast_error_sq N (primeFamilyWeight N a) (primeFamilyWeight N b)
    (pairLags N p q)
  have hc' : (pairContrast N a p q-pairContrast N b p q)^2 ≤
      64*∑ v : Fin 6 → Fin 2, (rawObservation N a p q v-rawObservation N b p q v)^2 := by
    simpa only [pairContrast, rawObservation, show (2 : ℝ)^6 = 64 by norm_num] using hc
  have hs := pairScale_lower N p q
  have hs2 : (6561 : ℝ) ≤ (pairScale N p q)^2 := by nlinarith
  calc
    _ ≤ (pairScale N p q)^2*(normalizedReadout N a p q-normalizedReadout N b p q)^2 :=
      mul_le_mul_of_nonneg_right hs2 (sq_nonneg _)
    _ = (pairContrast N a p q-pairContrast N b p q)^2 := by
      rw [normalizedReadout_eq, normalizedReadout_eq, pairContrast_eq, pairContrast_eq]
      ring
    _ ≤ _ := hc'

/-- Raw data control the entire normalized sixth-readout matrix. -/
theorem noise_comparison (N : ℕ) (a b : ℕ → ℝ) :
    6561*primeSixthNoise N a b ≤ 64*rawNoise N a b := by
  unfold primeSixthNoise rawNoise
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro q _
  simpa only [normalizedReadout_eq, normalizedPrimeSixthReadout_eq, Finset.mul_sum]
    using normalized_error_sq N a b p q

/-- One common orientation simultaneously satisfies all three reconstruction bounds in raw-data noise. -/
theorem raw_stability (N : ℕ) (a b : ℕ → ℝ) :
    let a' := fun p : oddPrimeModes N => a p
    let b' := fun p : oddPrimeModes N => b p
    (6561*(CubedGram.error6 a' b')^2 ≤ 32768*rawNoise N a b ∧
      6561*CubedGram.mass6 a' b'*CubedGram.error6 a' b' ≤ 2048*rawNoise N a b ∧
      6561*CubedGram.mass6 a' b'*CubedGram.weightedError a' b' ≤ 512*rawNoise N a b) ∨
    (6561*(CubedGram.error6 a' (fun p => -b' p))^2 ≤ 32768*rawNoise N a b ∧
      6561*CubedGram.mass6 a' b'*CubedGram.error6 a' (fun p => -b' p) ≤ 2048*rawNoise N a b ∧
      6561*CubedGram.mass6 a' b'*CubedGram.weightedError a' (fun p => -b' p) ≤ 512*rawNoise N a b) := by
  have hn := noise_comparison N a b
  rcases primeFamily_sixth_stability N a b with h | h
  · left
    rcases h with ⟨h1,h2,h3⟩
    exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · right
    rcases h with ⟨h1,h2,h3⟩
    exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.PrimeRaw
