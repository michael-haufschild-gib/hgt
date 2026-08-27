import GaloisForLFunctions.HTGeometry.AbelianZetaGas.DepthTail
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ParityMass

/-!
# Fermionic/odd-depth order duality

Euler's distinct-parts/odd-parts theorem identifies the complete order organ of the fermionic
prime-depth gas with that of the odd-depth bosonic sector.  The zeta ladder splits independently
into odd- and even-depth shells; the even shell is the doubled ladder.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Odd-depth bosonic zeta ladder `prod_{j odd} zeta(j sigma)`. -/
def oddDepthZetaPartition (σ : EulerSigma) : ℂ :=
  ∏' n : ℕ, riemannZeta (((((2 * n + 1 : ℕ) : ℝ) * σ.val : ℝ) : ℂ))

/-- Fermionic partition function, written as the exact square-shell quotient `Z(σ) / Z(2σ)`. -/
def fermionicZetaPartition (σ : EulerSigma) : ℂ :=
  (temperatureConv σ).zetaPartition / (temperatureConv σ.double).zetaPartition

private theorem hasProd_oddDepthZetaPartition (σ : EulerSigma) :
    HasProd (fun n : ℕ =>
      riemannZeta (((((2 * n + 1 : ℕ) : ℝ) * σ.val : ℝ) : ℂ)))
      (oddDepthZetaPartition σ) := by
  have hnorm := summable_norm_zeta_depth_sub_one σ.val 0 0 (by simpa using σ.pos)
  have htail := hnorm.comp_injective Nat.succ_injective
  have hoddNorm := htail.comp_injective
    (show Function.Injective (fun n : ℕ => 2 * n) by
      intro a b h
      exact Nat.eq_of_mul_eq_mul_left (by omega) h)
  have hs := summable_norm_iff.mp hoddNorm
  have hm : Multipliable (fun n : ℕ =>
      riemannZeta (((((2 * n + 1 : ℕ) : ℝ) * σ.val : ℝ) : ℂ))) := by
    convert Complex.multipliable_one_add_of_summable hs using 1
    funext n
    simp only [depthArg, Nat.succ_eq_add_one, add_zero]
    push_cast
    ring
  simpa only [oddDepthZetaPartition] using hm.hasProd

/-- **Euler duality, partition form.** Fermionic partition function equals odd-depth bosonic
partition function: `Z_F(σ) = prod_{j odd} zeta(jσ)`. -/
theorem fermionicZetaPartition_eq_oddDepth (σ : EulerSigma) :
    fermionicZetaPartition σ = oddDepthZetaPartition σ := by
  let f : ℕ → ℂ := fun n =>
    riemannZeta (((((n + 1 : ℕ) : ℝ) * σ.val : ℝ) : ℂ))
  have hfull : HasProd f (temperatureConv σ).zetaPartition := by
    simpa only [f, temperatureConv_sigma, temperatureConv_tau, add_zero] using
      (temperatureConv σ).hasProd_zetaLadder_zetaPartition
  have hodd : HasProd (fun n => f (2 * n)) (oddDepthZetaPartition σ) := by
    simpa only [f, Nat.reduceAdd] using hasProd_oddDepthZetaPartition σ
  have heven : HasProd (fun n => f (2 * n + 1))
      (temperatureConv σ.double).zetaPartition := by
    have h := (temperatureConv σ.double).hasProd_zetaLadder_zetaPartition
    convert h using 1
    funext n
    simp only [f, temperatureConv_sigma, temperatureConv_tau, add_zero, EulerSigma.double_val]
    congr 2
    push_cast
    ring
  have hsplit := hodd.even_mul_odd heven
  have hfactor : (temperatureConv σ).zetaPartition =
      oddDepthZetaPartition σ * (temperatureConv σ.double).zetaPartition :=
    hfull.unique hsplit
  rw [fermionicZetaPartition, div_eq_iff
    (AbelianZetaConvergentParameters.zetaPartition_ne_zero (temperatureConv σ.double))]
  exact hfactor

/-- Number of distinct-part configurations of order exponent `k`. -/
def fermionicOrderCoefficient (k : ℕ) : ℕ := (Nat.Partition.distincts k).card

/-- Number of odd-depth bosonic configurations of order exponent `k`. -/
def oddDepthOrderCoefficient (k : ℕ) : ℕ := (Nat.Partition.odds k).card

/-- Euler's partition theorem, in the exact coefficient orientation used by the order laws. -/
theorem fermionicOrderCoefficient_eq_oddDepth (k : ℕ) :
    fermionicOrderCoefficient k = oddDepthOrderCoefficient k := by
  exact (Nat.Partition.card_odds_eq_card_distincts k).symm

/-- Distinct-part coefficients admit the elementary subset bound needed for local normalization. -/
theorem fermionicOrderCoefficient_le_two_pow (k : ℕ) :
    fermionicOrderCoefficient k ≤ 2 ^ k := by
  let f : Nat.Partition k → Finset ℕ := fun P => P.parts.toFinset
  unfold fermionicOrderCoefficient
  calc
    (Nat.Partition.distincts k).card ≤ (Finset.Icc 1 k).powerset.card := by
      apply Finset.card_le_card_of_injOn f
      · intro P hP
        change f P ∈ (Finset.Icc 1 k).powerset
        rw [Finset.mem_powerset]
        intro b hb
        have hbparts : b ∈ P.parts := by simpa [f] using hb
        exact Finset.mem_Icc.mpr
          ⟨P.parts_pos hbparts, Nat.Partition.le_of_mem_parts hbparts⟩
      · intro P hP Q hQ heq
        have hPnodup : P.parts.Nodup := by
          simpa [Nat.Partition.distincts] using hP
        have hQnodup : Q.parts.Nodup := by
          simpa [Nat.Partition.distincts] using hQ
        apply Nat.Partition.ext
        have hPf : (⟨P.parts, hPnodup⟩ : Finset ℕ) = P.parts.toFinset :=
          Multiset.toFinset_eq hPnodup
        have hQf : (⟨Q.parts, hQnodup⟩ : Finset ℕ) = Q.parts.toFinset :=
          Multiset.toFinset_eq hQnodup
        exact congrArg Finset.val (hPf.trans (heq.trans hQf.symm))
    _ = 2 ^ k := by simp

/-- Local grand partition series determined by order coefficients. -/
def primeOrderPartition (c : ℕ → ℕ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' k : ℕ, (c k : ℝ≥0∞) * q ^ k

/-- Normalized local order mass attached to a coefficient sequence. -/
def primeOrderProbability (c : ℕ → ℕ) (q : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  (c k : ℝ≥0∞) * q ^ k / primeOrderPartition c q

/-- Nome on the prime fibre of the temperature gas. -/
def abelianZetaPrimeNome (σ : EulerSigma) (p : Nat.Primes) : ℝ≥0∞ :=
  ENNReal.ofReal ((temperatureConv σ).toAbelianZetaParameters.ratio (p, 0))

/-- Every prime nome at temperature `σ > 1` is strictly below `1/2`. -/
theorem abelianZetaPrimeRatio_lt_half (σ : EulerSigma) (p : Nat.Primes) :
    (temperatureConv σ).toAbelianZetaParameters.ratio (p, 0) < 1 / 2 := by
  have hp1 : (1 : ℝ) < p := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two p.prop.two_le)
  have hpow : (p : ℝ) ^ (-σ.val) < (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith [σ.one_lt])
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
    exact inv_anti₀ (by norm_num) (by exact_mod_cast p.prop.two_le)
  rw [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent]
  simp only [temperatureConv_sigma, temperatureConv_tau, AbelianZetaMode.depth, add_zero]
  rw [Real.rpow_neg_one] at hpow
  norm_num at hinv ⊢
  exact lt_of_lt_of_le hpow hinv

theorem primeOrderPartition_fermionic_ne_zero (σ : EulerSigma) (p : Nat.Primes) :
    primeOrderPartition fermionicOrderCoefficient (abelianZetaPrimeNome σ p) ≠ 0 := by
  have hone : (1 : ℝ≥0∞) ≤
      (fermionicOrderCoefficient 0 : ℝ≥0∞) * (abelianZetaPrimeNome σ p) ^ 0 := by
    simp [fermionicOrderCoefficient, Nat.Partition.distincts]
  have hle : (fermionicOrderCoefficient 0 : ℝ≥0∞) * (abelianZetaPrimeNome σ p) ^ 0 ≤
      primeOrderPartition fermionicOrderCoefficient (abelianZetaPrimeNome σ p) := by
    exact ENNReal.le_tsum 0
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (hone.trans hle))

theorem primeOrderPartition_fermionic_ne_top (σ : EulerSigma) (p : Nat.Primes) :
    primeOrderPartition fermionicOrderCoefficient (abelianZetaPrimeNome σ p) ≠ ∞ := by
  let r : ℝ := (temperatureConv σ).toAbelianZetaParameters.ratio (p, 0)
  have hr0 : 0 ≤ r := (temperatureConv σ).toAbelianZetaParameters.ratio_nonneg (p, 0)
  have hrhalf : r < 1 / 2 := abelianZetaPrimeRatio_lt_half σ p
  have hgeom : Summable fun k : ℕ => (2 * r) ^ k :=
    summable_geometric_of_lt_one (mul_nonneg (by norm_num) hr0) (by linarith)
  have hbound : primeOrderPartition fermionicOrderCoefficient (abelianZetaPrimeNome σ p) ≤
      ∑' k : ℕ, ENNReal.ofReal ((2 * r) ^ k) := by
    unfold primeOrderPartition
    apply ENNReal.tsum_le_tsum
    intro k
    rw [abelianZetaPrimeNome]
    calc
      (fermionicOrderCoefficient k : ℝ≥0∞) * ENNReal.ofReal r ^ k ≤
          ((2 ^ k : ℕ) : ℝ≥0∞) * ENNReal.ofReal r ^ k := by
        gcongr
        exact_mod_cast fermionicOrderCoefficient_le_two_pow k
      _ = ENNReal.ofReal ((2 * r) ^ k) := by
        rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k),
          ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_pow hr0]
        norm_num
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun k => pow_nonneg (mul_nonneg (by norm_num) hr0) k) hgeom] at hbound
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound

theorem primeOrderPartition_oddDepth_ne_zero (σ : EulerSigma) (p : Nat.Primes) :
    primeOrderPartition oddDepthOrderCoefficient (abelianZetaPrimeNome σ p) ≠ 0 := by
  have hc : oddDepthOrderCoefficient = fermionicOrderCoefficient :=
    funext fun k => (fermionicOrderCoefficient_eq_oddDepth k).symm
  rw [hc]
  exact primeOrderPartition_fermionic_ne_zero σ p

theorem primeOrderPartition_oddDepth_ne_top (σ : EulerSigma) (p : Nat.Primes) :
    primeOrderPartition oddDepthOrderCoefficient (abelianZetaPrimeNome σ p) ≠ ∞ := by
  have hc : oddDepthOrderCoefficient = fermionicOrderCoefficient :=
    funext fun k => (fermionicOrderCoefficient_eq_oddDepth k).symm
  rw [hc]
  exact primeOrderPartition_fermionic_ne_top σ p

/-- Fermionic order-exponent probability at one prime. -/
def fermionicPrimeOrderProbability (σ : EulerSigma) (p : Nat.Primes) (k : ℕ) : ℝ≥0∞ :=
  primeOrderProbability fermionicOrderCoefficient (abelianZetaPrimeNome σ p) k

/-- Odd-depth bosonic order-exponent probability at one prime. -/
def oddDepthPrimeOrderProbability (σ : EulerSigma) (p : Nat.Primes) (k : ℕ) : ℝ≥0∞ :=
  primeOrderProbability oddDepthOrderCoefficient (abelianZetaPrimeNome σ p) k

/-- **`(GAS4.3)`.** Fermionic and odd-depth bosonic prime-order laws agree at every exponent. -/
theorem fermionicPrimeOrderProbability_eq_oddDepth
    (σ : EulerSigma) (p : Nat.Primes) (k : ℕ) :
    fermionicPrimeOrderProbability σ p k = oddDepthPrimeOrderProbability σ p k := by
  simp only [fermionicPrimeOrderProbability, oddDepthPrimeOrderProbability,
    primeOrderProbability, primeOrderPartition, fermionicOrderCoefficient_eq_oddDepth]

/-- Atomic prime-order law associated to normalized coefficient masses. -/
def primeOrderLaw (c : ℕ → ℕ) (q : ℝ≥0∞) : Measure ℕ :=
  Measure.sum fun k => primeOrderProbability c q k • Measure.dirac k

theorem primeOrderLaw_univ (c : ℕ → ℕ) (q : ℝ≥0∞)
    (h0 : primeOrderPartition c q ≠ 0) (ht : primeOrderPartition c q ≠ ∞) :
    primeOrderLaw c q Set.univ = 1 := by
  rw [primeOrderLaw]
  simp only [Measure.sum_apply, MeasurableSet.univ, Measure.smul_apply, Measure.dirac_apply',
    Set.mem_univ, Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one,
    primeOrderProbability, div_eq_mul_inv, ENNReal.tsum_mul_right, primeOrderPartition]
  exact ENNReal.div_self h0 ht

instance fermionicPrimeOrderLaw_isProbability (σ : EulerSigma) (p : Nat.Primes) :
    IsProbabilityMeasure
      (primeOrderLaw fermionicOrderCoefficient (abelianZetaPrimeNome σ p)) :=
  ⟨primeOrderLaw_univ _ _ (primeOrderPartition_fermionic_ne_zero σ p)
    (primeOrderPartition_fermionic_ne_top σ p)⟩

instance oddDepthPrimeOrderLaw_isProbability (σ : EulerSigma) (p : Nat.Primes) :
    IsProbabilityMeasure
      (primeOrderLaw oddDepthOrderCoefficient (abelianZetaPrimeNome σ p)) :=
  ⟨primeOrderLaw_univ _ _ (primeOrderPartition_oddDepth_ne_zero σ p)
    (primeOrderPartition_oddDepth_ne_top σ p)⟩

/-- Fermionic full order law, assembled independently over primes. -/
def fermionicOrderLaw (σ : EulerSigma) : Measure (Nat.Primes → ℕ) :=
  Measure.infinitePi fun p => primeOrderLaw fermionicOrderCoefficient (abelianZetaPrimeNome σ p)

/-- Odd-depth bosonic full order law, assembled independently over primes. -/
def oddDepthBosonicOrderLaw (σ : EulerSigma) : Measure (Nat.Primes → ℕ) :=
  Measure.infinitePi fun p => primeOrderLaw oddDepthOrderCoefficient (abelianZetaPrimeNome σ p)

instance fermionicOrderLaw_isProbability (σ : EulerSigma) :
    IsProbabilityMeasure (fermionicOrderLaw σ) := by
  dsimp [fermionicOrderLaw]
  infer_instance

instance oddDepthBosonicOrderLaw_isProbability (σ : EulerSigma) :
    IsProbabilityMeasure (oddDepthBosonicOrderLaw σ) := by
  dsimp [oddDepthBosonicOrderLaw]
  infer_instance

/-- The complete order-observable laws coincide, not only their single-prime marginals. -/
theorem fermionicOrderLaw_eq_oddDepth (σ : EulerSigma) :
    fermionicOrderLaw σ = oddDepthBosonicOrderLaw σ := by
  have hc : fermionicOrderCoefficient = oddDepthOrderCoefficient :=
    funext fermionicOrderCoefficient_eq_oddDepth
  rw [fermionicOrderLaw, oddDepthBosonicOrderLaw, hc]

/-- Unique distinct-part configuration at order exponent two: one depth-two cyclic factor. -/
def cyclicOrderTwoPartition : Nat.Partition 2 where
  parts := {2}
  parts_pos := by simp
  parts_sum := by simp

/-- Unique odd-part configuration at order exponent two: two depth-one cyclic factors. -/
def elementaryOrderTwoPartition : Nat.Partition 2 where
  parts := {1, 1}
  parts_pos := by simp
  parts_sum := by simp

@[simp] theorem cyclicOrderTwoPartition_parts : cyclicOrderTwoPartition.parts = {2} := rfl

@[simp] theorem elementaryOrderTwoPartition_parts :
    elementaryOrderTwoPartition.parts = {1, 1} := rfl

/-- Distinct parts force the cyclic configuration at order exponent two. -/
theorem eq_cyclicOrderTwoPartition_of_mem_distincts
    (P : Nat.Partition 2) (hP : P ∈ Nat.Partition.distincts 2) :
    P = cyclicOrderTwoPartition := by
  have hnodup : P.parts.Nodup := by
    simpa [Nat.Partition.distincts] using hP
  have htwo : 2 ∈ P.parts := by
    by_contra htwo
    have hall : ∀ b ∈ P.parts, b = 1 := by
      intro b hb
      have hbpos := P.parts_pos hb
      have hble := Nat.Partition.le_of_mem_parts hb
      have hb12 : b = 1 ∨ b = 2 := by omega
      exact hb12.resolve_right fun hb2 => htwo (hb2 ▸ hb)
    have hrepl : P.parts = Multiset.replicate P.parts.card 1 :=
      (Multiset.eq_replicate_card).2 hall
    have hcard : P.parts.card = 2 := by
      have hsum := P.parts_sum
      rw [hrepl, Multiset.sum_replicate] at hsum
      simpa using hsum
    rw [hrepl, hcard] at hnodup
    simp at hnodup
  apply Nat.Partition.ext
  have hsumErase := Multiset.sum_erase htwo
  rw [P.parts_sum] at hsumErase
  have heraseSum : (P.parts.erase 2).sum = 0 := by omega
  have hcardLe : (P.parts.erase 2).card ≤ (P.parts.erase 2).sum := by
    simpa using Multiset.card_nsmul_le_sum (s := P.parts.erase 2) (a := 1)
      (fun b hb => P.parts_pos (Multiset.mem_of_mem_erase hb))
  have heraseCard : (P.parts.erase 2).card = 0 := by omega
  have herase : P.parts.erase 2 = 0 := Multiset.card_eq_zero.mp heraseCard
  have hcons := Multiset.cons_erase htwo
  rw [herase] at hcons
  simpa using hcons.symm

/-- Odd parts force the elementary-abelian configuration at order exponent two. -/
theorem eq_elementaryOrderTwoPartition_of_mem_odds
    (P : Nat.Partition 2) (hP : P ∈ Nat.Partition.odds 2) :
    P = elementaryOrderTwoPartition := by
  have hodd : ∀ b ∈ P.parts, ¬Even b := by
    simpa [Nat.Partition.odds, Nat.Partition.restricted] using hP
  have hall : ∀ b ∈ P.parts, b = 1 := by
    intro b hb
    have hbpos := P.parts_pos hb
    have hble := Nat.Partition.le_of_mem_parts hb
    have hb12 : b = 1 ∨ b = 2 := by omega
    exact hb12.resolve_right fun hb2 => hodd b hb (hb2 ▸ even_two)
  have hrepl : P.parts = Multiset.replicate P.parts.card 1 :=
    (Multiset.eq_replicate_card).2 hall
  have hcard : P.parts.card = 2 := by
    have hsum := P.parts_sum
    rw [hrepl, Multiset.sum_replicate] at hsum
    simpa using hsum
  apply Nat.Partition.ext
  rw [hrepl, hcard]
  rfl

/-- Fermionic order-two fibre has factor count one. -/
theorem card_parts_eq_one_of_mem_distincts_two
    (P : Nat.Partition 2) (hP : P ∈ Nat.Partition.distincts 2) :
    P.parts.card = 1 := by
  rw [eq_cyclicOrderTwoPartition_of_mem_distincts P hP]
  simp

/-- Odd-depth bosonic order-two fibre has factor count two. -/
theorem card_parts_eq_two_of_mem_odds_two
    (P : Nat.Partition 2) (hP : P ∈ Nat.Partition.odds 2) :
    P.parts.card = 2 := by
  rw [eq_elementaryOrderTwoPartition_of_mem_odds P hP]
  simp

/-- The order-`p²` conditioning event has positive probability in both sectors. -/
theorem orderTwo_conditioning_probabilities_pos (σ : EulerSigma) (p : Nat.Primes) :
    0 < fermionicPrimeOrderProbability σ p 2 ∧
      0 < oddDepthPrimeOrderProbability σ p 2 := by
  have hq : abelianZetaPrimeNome σ p ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      ((temperatureConv σ).toAbelianZetaParameters.ratio_pos (p, 0)))
  have hc : fermionicOrderCoefficient 2 ≠ 0 := by
    unfold fermionicOrderCoefficient
    rw [Finset.card_ne_zero]
    refine ⟨cyclicOrderTwoPartition, ?_⟩
    simp [Nat.Partition.distincts, cyclicOrderTwoPartition]
  have hfermion : 0 < fermionicPrimeOrderProbability σ p 2 := by
    unfold fermionicPrimeOrderProbability primeOrderProbability
    apply ENNReal.div_pos
    · exact mul_ne_zero (by exact_mod_cast hc) (pow_ne_zero 2 hq)
    · exact primeOrderPartition_fermionic_ne_top σ p
  exact ⟨hfermion, by
    rw [← fermionicPrimeOrderProbability_eq_oddDepth σ p 2]
    exact hfermion⟩

end

end GaloisForLFunctions.HTGeometry
