import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanSignedMarginal

/-!
# Complete coherent stars and source-row correction

A normalized indicator profile on a growing complete prime set gives an actual
coherent Frobenius packet with trace zero and marginal variation at most two.
Its ambient and one-leg graph limits are zero, while its prime marginal tends
to a point mass and its reciprocal energy tends to the corresponding fixed
prime weight. The exact squared ambient norm is `2 * (card(s) - 1) / card(s)^(2 : ℕ)`.

Subtracting this complete coherent packet from the genuine fixed-left normalized
Big-Witt row preserves trace one and its singular graph limit. Its marginal
becomes the uniform measure on the growing prime set, so all fixed coefficients
and reciprocal energy vanish. This explicit correction loses prime retention;
it does not establish source-to-physical reader agreement or RH.
-/

open Complex Filter Function Set Topology
open scoped BigOperators
namespace RHTower.HedenmalmThetaSource
noncomputable section

set_option backward.isDefEq.respectTransparency false in
theorem deningerBigWittCrossPairFiniteRightLegPacket_apply
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes)
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPairFiniteRightLegPacket a s i =
      if i.1.1 ∈ s ∧ i.1.2 ∈ s then
        deningerBigWittCrossPairRightLeg a i.1.1 i.1.2 else 0 := by
  classical
  rcases i with ⟨⟨p,q⟩, hpq⟩
  rw [deningerBigWittCrossPairFiniteRightLegPacket]
  simp only [Finsupp.finsetSum_apply]
  trans ∑ r ∈ s, ∑ t ∈ s,
    if r = p ∧ t = q then deningerBigWittCrossPairRightLeg a p q else 0
  · apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hrt : r ≠ t
    · simp only [dif_pos hrt]
      rw [Finsupp.single_apply]
      have heq : (⟨(r,t),hrt⟩ : DeningerCalderonWittCrossPrimePacketIndex) =
          ⟨(p,q),hpq⟩ ↔ r = p ∧ t = q := by
        constructor
        · intro h
          exact Prod.mk.inj (congrArg Subtype.val h)
        · rintro ⟨rfl,rfl⟩
          rfl
      rw [heq]
      split_ifs with h
      · rcases h with ⟨rfl,rfl⟩
        rfl
      · rfl
    · have hnot : ¬(r = p ∧ t = q) := by
        rintro ⟨rfl,rfl⟩
        exact hrt hpq
      simp [hrt, hnot]
  · by_cases hp : p ∈ s <;> by_cases hq : q ∈ s <;>
      simp [ite_and, hp, hq]

set_option backward.isDefEq.respectTransparency false in
theorem norm_sq_deningerBigWittCrossPairFinitePacketAdmission_coherent
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    ‖deningerBigWittCrossPairFinitePacketAdmission
      (deningerBigWittCrossPairFiniteRightLegPacket a s)‖ ^ (2 : ℕ) =
      ∑ p ∈ s, ∑ q ∈ s, ‖a p - a q‖ ^ (2 : ℕ) := by
  classical
  let t : Finset DeningerCalderonWittCrossPrimePacketIndex :=
    (s ×ˢ s).subtype (fun i : Nat.Primes × Nat.Primes => i.1 ≠ i.2)
  have ht (i : DeningerCalderonWittCrossPrimePacketIndex) :
      i ∈ t ↔ i.1.1 ∈ s ∧ i.1.2 ∈ s := by
    rcases i with ⟨⟨p,q⟩,hpq⟩
    exact (Finset.mem_subtype (a := (⟨(p,q),hpq⟩ :
      {i : Nat.Primes × Nat.Primes // i.1 ≠ i.2}))).trans Finset.mem_product
  have heval : (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
      ‖(deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittCrossPairFiniteRightLegPacket a s)) i‖ ^ (2 : ℕ)) =
      fun i => ‖if i.1.1 ∈ s ∧ i.1.2 ∈ s then
        deningerBigWittCrossPairRightLeg a i.1.1 i.1.2 else 0‖ ^ (2 : ℕ) := by
    funext i
    rw [show (deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittCrossPairFiniteRightLegPacket a s)) i =
        deningerBigWittCrossPairFiniteRightLegPacket a s i from
      deningerBigWittCrossPairFinitePacketAdmissionToFun_apply _ _,
      deningerBigWittCrossPairFiniteRightLegPacket_apply]
  rw [HilbertSchmidt.lp_norm_sq_eq, heval]
  rw [tsum_eq_sum (s := t) (fun i hi => by simp [(ht i).not.mp hi])]
  have heq : (∑ i ∈ t, ‖if i.1.1 ∈ s ∧ i.1.2 ∈ s then
      deningerBigWittCrossPairRightLeg a i.1.1 i.1.2 else 0‖ ^ (2 : ℕ)) =
      ∑ i ∈ t, ‖a i.1.1 - a i.1.2‖ ^ (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos ((ht i).mp hi), deningerBigWittCrossPairRightLeg, Complex.norm_conj]
  rw [heq]
  change (∑ i ∈ (s ×ˢ s).subtype (fun i : Nat.Primes × Nat.Primes => i.1 ≠ i.2), ‖a i.1.1 - a i.1.2‖ ^ (2 : ℕ)) = _
  rw [Finset.sum_subtype_eq_sum_filter
    (fun i : Nat.Primes × Nat.Primes => ‖a i.1 - a i.2‖ ^ (2 : ℕ)), Finset.sum_filter]
  have hf : (fun i : Nat.Primes × Nat.Primes =>
      if i.1 ≠ i.2 then ‖a i.1 - a i.2‖ ^ (2 : ℕ) else 0) =
      fun i => ‖a i.1 - a i.2‖ ^ (2 : ℕ) := by
    funext i
    by_cases hi : i.1 = i.2 <;> simp [hi]
  rw [hf, Finset.sum_product]

def deningerBigWittCoherentStar (p : Nat.Primes) (s : Finset Nat.Primes) :
    DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  ((s.card : ℂ)⁻¹) • deningerBigWittCrossPairFiniteRightLegPacket
    (fun q => if q = p then 1 else 0) s

theorem deningerBigWittCoherentStar_marginal (p : Nat.Primes)
    (s : Finset Nat.Primes) (hp : p ∈ s) (q : Nat.Primes) :
    deningerBigWittLeftPrimeMarginal (deningerBigWittCoherentStar p s) q =
      (if q = p then 1 else 0) - (if q ∈ s then (s.card : ℂ)⁻¹ else 0) := by
  classical
  have hcard : (s.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨p,hp⟩).ne'
  rw [deningerBigWittCoherentStar, deningerBigWittLeftPrimeMarginal_smul,
    Finsupp.smul_apply, deningerBigWittLeftPrimeMarginal_coherent]
  by_cases hqp : q = p <;> by_cases hqs : q ∈ s <;>
    simp [hqp, hqs, hp, smul_eq_mul, mul_sub, hcard]

theorem deningerBigWittCoherentStar_trace (p : Nat.Primes) (s : Finset Nat.Primes) :
    deningerBigWittCrossPairAlgebraicOneLegTrace (deningerBigWittCoherentStar p s) = 0 := by
  rw [deningerBigWittCoherentStar, map_smul,
    deningerBigWittCrossPairAlgebraicOneLegTrace_finiteRightLegPacket, smul_zero]

theorem norm_sq_deningerBigWittCoherentStar (p : Nat.Primes)
    (s : Finset Nat.Primes) (hp : p ∈ s) :
    ‖deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCoherentStar p s)‖ ^ (2 : ℕ) =
      2 * ((s.card : ℝ) - 1) / (s.card : ℝ) ^ (2 : ℕ) := by
  classical
  let b : Nat.Primes → ℝ := fun q => if q = p then 1 else 0
  have hb : ∑ q ∈ s, b q = 1 := by simp [b, hp]
  have hterm (r t : Nat.Primes) :
      ‖(if r = p then (1 : ℂ) else 0) - (if t = p then 1 else 0)‖ ^ (2 : ℕ) =
      b r + b t - 2 * b r * b t := by
    by_cases hr : r = p <;> by_cases ht : t = p <;> norm_num [b, hr, ht]
  rw [deningerBigWittCoherentStar, map_smul, norm_smul, mul_pow,
    norm_inv, Complex.norm_natCast,
    norm_sq_deningerBigWittCrossPairFinitePacketAdmission_coherent]
  simp_rw [hterm]
  have hsum : (∑ r ∈ s, ∑ t ∈ s, (b r + b t - 2 * b r * b t)) =
      2 * ((s.card : ℝ) - 1) := by
    simp [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hb, nsmul_eq_mul]
    ring
  rw [hsum]
  ring

def finitePrimeUniformMarginal (s : Finset Nat.Primes) : Nat.Primes →₀ ℂ :=
  Finsupp.indicator s (fun _ _ => (s.card : ℂ)⁻¹)

theorem finitePrimeUniformMarginal_variation (s : Finset Nat.Primes) (hs : s.Nonempty) :
    finitePrimeMarginalVariation (finitePrimeUniformMarginal s) = 1 := by
  classical
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hs).ne'
  rw [show finitePrimeMarginalVariation (finitePrimeUniformMarginal s) =
      ∑ p ∈ s, ‖finitePrimeUniformMarginal s p‖ from
    Finsupp.sum_of_support_subset _ (Finsupp.support_indicator_subset s (fun _ _ => (s.card : ℂ)⁻¹))
      (fun _ z => ‖z‖) (fun _ _ => norm_zero)]
  have hnorm : ∀ p ∈ s, ‖finitePrimeUniformMarginal s p‖ = (s.card : ℝ)⁻¹ := by
    intro p hp
    simp [finitePrimeUniformMarginal, Finsupp.indicator_apply, hp]
  simp_rw [Finset.sum_congr rfl hnorm]
  simp [nsmul_eq_mul, hcard]

theorem deningerBigWittCoherentStar_marginal_eq (p : Nat.Primes)
    (s : Finset Nat.Primes) (hp : p ∈ s) :
    deningerBigWittLeftPrimeMarginal (deningerBigWittCoherentStar p s) =
      Finsupp.single p 1 - finitePrimeUniformMarginal s := by
  classical
  ext q
  rw [deningerBigWittCoherentStar_marginal p s hp]
  simp [finitePrimeUniformMarginal, Finsupp.indicator_apply, Finsupp.single_apply, eq_comm]

theorem deningerBigWittCoherentStar_marginal_variation_le_two (p : Nat.Primes)
    (s : Finset Nat.Primes) (hp : p ∈ s) :
    finitePrimeMarginalVariation
      (deningerBigWittLeftPrimeMarginal (deningerBigWittCoherentStar p s)) ≤ 2 := by
  rw [deningerBigWittCoherentStar_marginal_eq p s hp]
  have h := finitePrimeMarginalVariation_sub_le (Finsupp.single p 1) (finitePrimeUniformMarginal s)
  rw [finitePrimeUniformMarginal_variation s ⟨p,hp⟩] at h
  have hsingle : finitePrimeMarginalVariation (Finsupp.single p 1) = 1 := by
    simp [finitePrimeMarginalVariation]
  simpa only [hsingle, one_add_one_eq_two] using h


theorem deningerBigWittCrossPairFiniteRightLegPacket_smul_profile
    (z : ℂ) (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittCrossPairFiniteRightLegPacket (fun p => z * a p) s =
      (starRingEnd ℂ) z • deningerBigWittCrossPairFiniteRightLegPacket a s := by
  classical
  ext i
  simp only [deningerBigWittCrossPairFiniteRightLegPacket_apply, Finsupp.smul_apply]
  by_cases hi : i.1.1 ∈ s ∧ i.1.2 ∈ s <;>
    simp [hi, deningerBigWittCrossPairRightLeg, ← mul_sub, map_mul, smul_eq_mul]

theorem deningerBigWittCoherentStar_is_complete (p : Nat.Primes) (s : Finset Nat.Primes) :
    ∃ a : Nat.Primes → ℂ,
      deningerBigWittCoherentStar p s = deningerBigWittCrossPairFiniteRightLegPacket a s := by
  classical
  refine ⟨fun q => (starRingEnd ℂ) ((s.card : ℂ)⁻¹) * (if q = p then 1 else 0), ?_⟩
  rw [deningerBigWittCrossPairFiniteRightLegPacket_smul_profile]
  simp [deningerBigWittCoherentStar]

theorem finitePrimeUniformMarginal_norm_le (s : Finset Nat.Primes) (p : Nat.Primes) :
    ‖finitePrimeUniformMarginal s p‖ ≤ (s.card : ℝ)⁻¹ := by
  classical
  by_cases hp : p ∈ s
  · simp [finitePrimeUniformMarginal, hp]
  · simp only [finitePrimeUniformMarginal, Finsupp.indicator_apply, dif_neg hp, norm_zero]
    positivity

theorem tendsto_finitePrimeUniformMarginal (s : ℕ → Finset Nat.Primes)
    (hcard : Tendsto (fun n => ((s n).card : ℝ)) atTop atTop) (p : Nat.Primes) :
    Tendsto (fun n => finitePrimeUniformMarginal (s n) p) atTop (nhds 0) := by
  apply squeeze_zero_norm (fun n => finitePrimeUniformMarginal_norm_le (s n) p)
  exact tendsto_inv_atTop_zero.comp hcard

theorem tendsto_deningerBigWittCoherentStar_marginal (p : Nat.Primes)
    (s : ℕ → Finset Nat.Primes) (hp : ∀ n, p ∈ s n)
    (hcard : Tendsto (fun n => ((s n).card : ℝ)) atTop atTop) (q : Nat.Primes) :
    Tendsto (fun n => deningerBigWittLeftPrimeMarginal (deningerBigWittCoherentStar p (s n)) q)
      atTop (nhds ((Finsupp.single p 1 : Nat.Primes →₀ ℂ) q)) := by
  simp_rw [deningerBigWittCoherentStar_marginal_eq p _ (hp _), Finsupp.sub_apply]
  simpa using (tendsto_const_nhds.sub (tendsto_finitePrimeUniformMarginal s hcard q))

theorem norm_sq_deningerBigWittCoherentStar_le (p : Nat.Primes)
    (s : Finset Nat.Primes) (hp : p ∈ s) :
    ‖deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCoherentStar p s)‖ ^ (2 : ℕ) ≤
      2 / (s.card : ℝ) := by
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨p,hp⟩).ne'
  rw [norm_sq_deningerBigWittCoherentStar p s hp]
  calc
    _ ≤ (2 * (s.card : ℝ)) / (s.card : ℝ) ^ (2 : ℕ) :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = _ := by field_simp

theorem tendsto_deningerBigWittCoherentStar_ambient (p : Nat.Primes)
    (s : ℕ → Finset Nat.Primes) (hp : ∀ n, p ∈ s n)
    (hcard : Tendsto (fun n => ((s n).card : ℝ)) atTop atTop) :
    Tendsto (fun n => deningerBigWittCrossPairFinitePacketAdmission
      (deningerBigWittCoherentStar p (s n))) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hcard.eventually (eventually_gt_atTop (2 / ε ^ (2 : ℕ)))] with n hn
  have hN : (0 : ℝ) < (s n).card := by exact_mod_cast Finset.card_pos.mpr ⟨p,hp n⟩
  have hsmall : 2 / ((s n).card : ℝ) < ε ^ (2 : ℕ) := by
    apply (div_lt_iff₀ hN).mpr
    have h := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hn
    nlinarith
  have hbound := (norm_sq_deningerBigWittCoherentStar_le p (s n) (hp n)).trans_lt hsmall
  rw [dist_zero_right]
  nlinarith [norm_nonneg (deningerBigWittCrossPairFinitePacketAdmission
    (deningerBigWittCoherentStar p (s n)))]

theorem tendsto_deningerBigWittCoherentStar_graph (p : Nat.Primes)
    (s : ℕ → Finset Nat.Primes) (hp : ∀ n, p ∈ s n)
    (hcard : Tendsto (fun n => ((s n).card : ℝ)) atTop atTop) :
    Tendsto (fun n => deningerBigWittCrossPairFiniteOneLegGraphAdmission
      (deningerBigWittCoherentStar p (s n))) atTop (nhds 0) := by
  have hpair : Tendsto (fun n =>
      (deningerBigWittCrossPairFinitePacketAdmission (deningerBigWittCoherentStar p (s n)),
        deningerBigWittCrossPairAlgebraicOneLegTrace (deningerBigWittCoherentStar p (s n))))
      atTop (nhds ((0 : DeningerCalderonWittCrossPrimePacketHilbert), (0 : ℂ))) := by
    simpa only [nhds_prod_eq] using (tendsto_deningerBigWittCoherentStar_ambient p s hp hcard).prodMk
      (by simpa only [deningerBigWittCoherentStar_trace]
          using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds 0)))
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ
    DeningerCalderonWittCrossPrimePacketHilbert ℂ).symm.continuous.tendsto _).comp hpair

theorem tendsto_deningerBigWittCoherentStar_energy (A : ℝ) (p : Nat.Primes)
    (s : ℕ → Finset Nat.Primes) (hp : ∀ n, p ∈ s n)
    (hcard : Tendsto (fun n => ((s n).card : ℝ)) atTop atTop) :
    Tendsto (fun n => primeLabelledEnergyReporter (fun q => A / (q : ℕ))
      (deningerBigWittCoherentStar p (s n))) atTop (nhds ((A / (p : ℕ) : ℝ) : ℂ)) := by
  have h := tendsto_primeLabelledEnergyReporter_of_marginals A
    (fun n => deningerBigWittCoherentStar p (s n)) 2 (by positivity)
    (fun n => deningerBigWittCoherentStar_marginal_variation_le_two p (s n) (hp n))
    (Finsupp.single p 1) (tendsto_deningerBigWittCoherentStar_marginal p s hp hcard)
  simpa [finitePrimeMarginalEnergy] using h

def deningerBigWittCoherentStarPrimeSet (p : Nat.Primes) (n : ℕ) : Finset Nat.Primes :=
  insert p ((Finset.range n).map ⟨nthPrimeSubtype, nthPrimeSubtype_injective⟩)

theorem deningerBigWittCoherentStarPrimeSet_mem (p : Nat.Primes) (n : ℕ) :
    p ∈ deningerBigWittCoherentStarPrimeSet p n := by
  classical
  simp [deningerBigWittCoherentStarPrimeSet]

theorem tendsto_deningerBigWittCoherentStarPrimeSet_card (p : Nat.Primes) :
    Tendsto (fun n => ((deningerBigWittCoherentStarPrimeSet p n).card : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
  intro n
  have h := Finset.card_le_card (Finset.subset_insert p
    ((Finset.range n).map ⟨nthPrimeSubtype, nthPrimeSubtype_injective⟩))
  exact_mod_cast (by simpa [deningerBigWittCoherentStarPrimeSet] using h)

def deningerBigWittCoherentStarSequence (p : Nat.Primes) (n : ℕ) :
    DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  deningerBigWittCoherentStar p (deningerBigWittCoherentStarPrimeSet p n)


/-- A source-only complete coherent sequence can be graph-null while retaining a prime marginal. -/
theorem deningerBigWittCoherentStarSequence_spec (p : Nat.Primes) :
    (∀ n, ∃ a : Nat.Primes → ℂ,
      deningerBigWittCoherentStarSequence p n =
        deningerBigWittCrossPairFiniteRightLegPacket a (deningerBigWittCoherentStarPrimeSet p n)) ∧
    (∀ n, deningerBigWittCrossPairAlgebraicOneLegTrace
      (deningerBigWittCoherentStarSequence p n) = 0) ∧
    (∀ n, finitePrimeMarginalVariation
      (deningerBigWittLeftPrimeMarginal (deningerBigWittCoherentStarSequence p n)) ≤ 2) ∧
    (∀ q, Tendsto (fun n => deningerBigWittLeftPrimeMarginal
      (deningerBigWittCoherentStarSequence p n) q) atTop
        (nhds ((Finsupp.single p 1 : Nat.Primes →₀ ℂ) q))) ∧
    Tendsto (fun n => deningerBigWittCrossPairFiniteOneLegGraphAdmission
      (deningerBigWittCoherentStarSequence p n)) atTop (nhds 0) ∧
    (∀ A : ℝ, Tendsto (fun n => primeLabelledEnergyReporter (fun q => A / (q : ℕ))
      (deningerBigWittCoherentStarSequence p n)) atTop (nhds ((A / (p : ℕ) : ℝ) : ℂ))) := by
  exact ⟨fun n => deningerBigWittCoherentStar_is_complete p _,
    fun n => deningerBigWittCoherentStar_trace p _,
    fun n => deningerBigWittCoherentStar_marginal_variation_le_two p _
      (deningerBigWittCoherentStarPrimeSet_mem p n),
    tendsto_deningerBigWittCoherentStar_marginal p _
      (deningerBigWittCoherentStarPrimeSet_mem p) (tendsto_deningerBigWittCoherentStarPrimeSet_card p),
    tendsto_deningerBigWittCoherentStar_graph p _
      (deningerBigWittCoherentStarPrimeSet_mem p) (tendsto_deningerBigWittCoherentStarPrimeSet_card p),
    fun A => tendsto_deningerBigWittCoherentStar_energy A p _
      (deningerBigWittCoherentStarPrimeSet_mem p) (tendsto_deningerBigWittCoherentStarPrimeSet_card p)⟩

theorem deningerBigWittLeftPrimeMarginal_sub
    (f g : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    deningerBigWittLeftPrimeMarginal (f - g) =
      deningerBigWittLeftPrimeMarginal f - deningerBigWittLeftPrimeMarginal g := by
  exact Finsupp.mapDomain_sub

theorem deningerBigWittLeftPrimeMarginal_woldFixedLeftRightEdgeNormalizedPacket (a n : ℕ) :
    deningerBigWittLeftPrimeMarginal (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n) =
      Finsupp.single (nthPrimeSubtype a) 1 := by
  classical
  ext p
  have h := primeLabelledEnergyReporter_woldFixedLeftRightEdgeNormalizedPacket
    (fun r => if r = p then 1 else 0) a n
  rw [primeLabelledEnergyReporter_eq_marginal] at h
  have hcast (r : Nat.Primes) : ((if r = p then 1 else 0 : ℝ) : ℂ) =
      if r = p then 1 else 0 := by split_ifs <;> rfl
  have hread (m : Nat.Primes →₀ ℂ) :
      finitePrimeMarginalEnergy (fun r => if r = p then 1 else 0) m = m p := by
    simp only [finitePrimeMarginalEnergy, Finsupp.sum, hcast, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq']
    by_cases hp : m p = 0 <;> simp [Finsupp.mem_support_iff, hp]
  rw [hread, hcast] at h
  simpa only [Finsupp.single_apply] using h

/-- Subtract the complete coherent star from the genuine fixed-left normalized row. -/
def deningerBigWittCoherentStarCorrectedRow (a n : ℕ) :
    DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n -
    deningerBigWittCoherentStarSequence (nthPrimeSubtype a) n

/-- The correction replaces the retained point mass by a uniform prime marginal. -/
theorem deningerBigWittCoherentStarCorrectedRow_marginal (a n : ℕ) :
    deningerBigWittLeftPrimeMarginal (deningerBigWittCoherentStarCorrectedRow a n) =
      finitePrimeUniformMarginal (deningerBigWittCoherentStarPrimeSet (nthPrimeSubtype a) n) := by
  rw [deningerBigWittCoherentStarCorrectedRow, deningerBigWittLeftPrimeMarginal_sub,
    deningerBigWittLeftPrimeMarginal_woldFixedLeftRightEdgeNormalizedPacket,
    deningerBigWittCoherentStarSequence,
    deningerBigWittCoherentStar_marginal_eq _ _ (deningerBigWittCoherentStarPrimeSet_mem _ _)]
  abel

theorem deningerBigWittCoherentStarCorrectedRow_trace (a n : ℕ) :
    deningerBigWittCrossPairAlgebraicOneLegTrace (deningerBigWittCoherentStarCorrectedRow a n) = 1 := by
  rw [deningerBigWittCoherentStarCorrectedRow, map_sub,
    deningerBigWittCrossPairAlgebraicOneLegTrace_woldFixedLeftRightEdgeNormalizedPacket,
    deningerBigWittCoherentStarSequence, deningerBigWittCoherentStar_trace, sub_zero]

theorem deningerBigWittCoherentStarCorrectedRow_variation (a n : ℕ) :
    finitePrimeMarginalVariation
      (deningerBigWittLeftPrimeMarginal (deningerBigWittCoherentStarCorrectedRow a n)) = 1 := by
  rw [deningerBigWittCoherentStarCorrectedRow_marginal]
  exact finitePrimeUniformMarginal_variation _
    ⟨nthPrimeSubtype a, deningerBigWittCoherentStarPrimeSet_mem _ _⟩

theorem tendsto_deningerBigWittCoherentStarCorrectedRow_marginal (a : ℕ) (p : Nat.Primes) :
    Tendsto (fun n => deningerBigWittLeftPrimeMarginal
      (deningerBigWittCoherentStarCorrectedRow a n) p) atTop (nhds 0) := by
  simp_rw [deningerBigWittCoherentStarCorrectedRow_marginal]
  exact tendsto_finitePrimeUniformMarginal _ (tendsto_deningerBigWittCoherentStarPrimeSet_card _) p

theorem tendsto_deningerBigWittCoherentStarCorrectedRow_graph (a : ℕ) :
    Tendsto (fun n => deningerBigWittCrossPairFiniteOneLegGraphAdmission
      (deningerBigWittCoherentStarCorrectedRow a n)) atTop
        (nhds deningerBigWittCrossPairOneLegGraphSingularVector) := by
  have h :=
    (tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_woldFixedLeftRightEdgeNormalizedPacket a).sub
      (deningerBigWittCoherentStarSequence_spec (nthPrimeSubtype a)).2.2.2.2.1
  simpa only [deningerBigWittCoherentStarCorrectedRow, map_sub, sub_zero] using h

theorem tendsto_deningerBigWittCoherentStarCorrectedRow_energy (A : ℝ) (a : ℕ) :
    Tendsto (fun n => primeLabelledEnergyReporter (fun p => A / (p : ℕ))
      (deningerBigWittCoherentStarCorrectedRow a n)) atTop (nhds 0) := by
  have h := tendsto_primeLabelledEnergyReporter_of_marginals A
    (deningerBigWittCoherentStarCorrectedRow a) 1 zero_le_one
    (fun n => (deningerBigWittCoherentStarCorrectedRow_variation a n).le) 0
    (by simpa using tendsto_deningerBigWittCoherentStarCorrectedRow_marginal a)
  simpa [finitePrimeMarginalEnergy] using h


end
end RHTower.HedenmalmThetaSource
