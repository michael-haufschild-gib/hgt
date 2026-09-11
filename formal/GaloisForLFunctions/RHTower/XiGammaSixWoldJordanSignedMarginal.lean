import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanCoherentMarginal

/-!
# Signed prime marginals and the fixed energy reader

The literal edge reporter factors through the left-prime marginal. Reciprocal
weights tend to zero along the prime boundary, so convergence to a finite marginal
preserves the reporter when marginal total variation stays bounded. A tail above
`B` pays at least `B * |energy|` in coefficient-weighted variation.

For the complete coherent Frobenius packet, the marginal is an exact finite
Laplacian. It vanishes precisely when the packet does, and its variation dominates
`card(s) * |a(p)-a(q)|`. Uniform variation over all finite prime sets is equivalent
to a constant profile. These source identities and analytic implications do not
assert the missing arithmetic comparison or prove RH.
-/

open Complex Filter Function Set Topology
open scoped BigOperators
namespace RHTower.HedenmalmThetaSource
noncomputable section

/-- Sum all right-edge coefficients at each retained left prime. -/
def deningerBigWittLeftPrimeMarginal
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) : Nat.Primes →₀ ℂ :=
  f.mapDomain fun i => i.1.1

/-- Total variation after right-edge contraction; internal cancellations are retained. -/
def finitePrimeMarginalVariation (m : Nat.Primes →₀ ℂ) : ℝ :=
  ∑ p ∈ m.support, ‖m p‖

/-- The fixed weighted reader on a finite prime marginal. -/
def finitePrimeMarginalEnergy (c : Nat.Primes → ℝ) (m : Nat.Primes →₀ ℂ) : ℂ :=
  m.sum fun p z => (c p : ℂ) * z

/-- Exact factorization of the original edge reader, before taking limits. -/
theorem primeLabelledEnergyReporter_eq_marginal (c : Nat.Primes → ℝ)
    (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    primeLabelledEnergyReporter c f =
      finitePrimeMarginalEnergy c (deningerBigWittLeftPrimeMarginal f) := by
  rw [finitePrimeMarginalEnergy, deningerBigWittLeftPrimeMarginal,
    Finsupp.sum_mapDomain_index (fun p => mul_zero _) (fun p x y => mul_add _ _ _)]
  simp [primeLabelledEnergyReporter, Finsupp.lsum_apply, Finsupp.sum,
    LinearMap.toSpanSingleton, mul_comm]

theorem finitePrimeMarginalEnergy_norm_le (c : Nat.Primes → ℝ)
    (m : Nat.Primes →₀ ℂ) (K : ℝ) (hK : ∀ p ∈ m.support, |c p| ≤ K) :
    ‖finitePrimeMarginalEnergy c m‖ ≤ K * finitePrimeMarginalVariation m := by
  classical
  unfold finitePrimeMarginalEnergy Finsupp.sum finitePrimeMarginalVariation
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hK p hp) (norm_nonneg _)

/-- Decaying reciprocal weights bound every signed or complex tail. -/
theorem finitePrimeMarginalEnergy_tail_bound (A : ℝ) (B : ℕ) (hB : 0 < B)
    (m : Nat.Primes →₀ ℂ) (hm : ∀ p ∈ m.support, B ≤ (p : ℕ)) :
    ‖finitePrimeMarginalEnergy (fun p => A / (p : ℕ)) m‖ ≤
      (|A| / B) * finitePrimeMarginalVariation m := by
  apply finitePrimeMarginalEnergy_norm_le
  intro p hp
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  rw [abs_div, abs_of_pos hp0]
  exact div_le_div_of_nonneg_left (abs_nonneg A) (by exact_mod_cast hB)
    (by exact_mod_cast hm p hp)

/-- A fixed nonzero tail correction requires variation growing with its minimum prime. -/
theorem finitePrimeMarginalEnergy_tail_cost (A : ℝ) (B : ℕ) (hB : 0 < B)
    (m : Nat.Primes →₀ ℂ) (hm : ∀ p ∈ m.support, B ≤ (p : ℕ)) :
    (B : ℝ) * ‖finitePrimeMarginalEnergy (fun p => A / (p : ℕ)) m‖ ≤
      |A| * finitePrimeMarginalVariation m := by
  have h := mul_le_mul_of_nonneg_left
    (finitePrimeMarginalEnergy_tail_bound A B hB m hm)
    (show (0 : ℝ) ≤ B by positivity)
  calc
    _ ≤ (B : ℝ) * ((|A| / B) * finitePrimeMarginalVariation m) := h
    _ = _ := by
      have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
      field_simp

/-- The actual coherent marginal is the complete-graph Laplacian of the conjugate profile. -/
theorem deningerBigWittLeftPrimeMarginal_coherent
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p : Nat.Primes) :
    deningerBigWittLeftPrimeMarginal (deningerBigWittCrossPairFiniteRightLegPacket a s) p =
      if p ∈ s then (s.card : ℂ) * (starRingEnd ℂ) (a p) -
        ∑ q ∈ s, (starRingEnd ℂ) (a q) else 0 := by
  classical
  have h := primeLabelledEnergyReporter_coherent_covariance
    (fun r => if r = p then 1 else 0) a s
  rw [primeLabelledEnergyReporter_eq_marginal] at h
  have hcast (r : Nat.Primes) : ((if r = p then 1 else 0 : ℝ) : ℂ) =
      if r = p then 1 else 0 := by split_ifs <;> rfl
  have hread (m : Nat.Primes →₀ ℂ) :
      finitePrimeMarginalEnergy (fun r => if r = p then 1 else 0) m = m p := by
    simp only [finitePrimeMarginalEnergy, Finsupp.sum, hcast, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq']
    by_cases hp : m p = 0 <;> simp [Finsupp.mem_support_iff, hp]
  rw [hread] at h
  simp_rw [hcast, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq'] at h
  by_cases hp : p ∈ s <;> simpa [hp] using h

/-- A complete coherent correction preserving every zero marginal is itself zero. -/
theorem deningerBigWittLeftPrimeMarginal_coherent_eq_zero_iff
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) :
    deningerBigWittLeftPrimeMarginal (deningerBigWittCrossPairFiniteRightLegPacket a s) = 0 ↔
      deningerBigWittCrossPairFiniteRightLegPacket a s = 0 := by
  classical
  constructor
  · intro hm
    rw [deningerBigWittCrossPairFiniteRightLegPacket]
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q hq
    split_ifs with hpq
    · have hp' := congrArg (fun m : Nat.Primes →₀ ℂ => m p) hm
      have hq' := congrArg (fun m : Nat.Primes →₀ ℂ => m q) hm
      rw [deningerBigWittLeftPrimeMarginal_coherent, if_pos hp] at hp'
      rw [deningerBigWittLeftPrimeMarginal_coherent, if_pos hq] at hq'
      have hcard : (s.card : ℂ) ≠ 0 := by
        exact_mod_cast (Finset.card_pos.mpr ⟨p, hp⟩).ne'
      have hdiff : (s.card : ℂ) *
          ((starRingEnd ℂ) (a p) - (starRingEnd ℂ) (a q)) = 0 := by
        change _ = 0 at hp' hq'
        linear_combination hp' - hq'
      have heq := (mul_eq_zero.mp hdiff).resolve_left hcard
      simp [deningerBigWittCrossPairRightLeg, map_sub, heq]
    · rfl
  · intro h
    simp [h, deningerBigWittLeftPrimeMarginal]

theorem finitePrimeMarginalVariation_nonneg (m : Nat.Primes →₀ ℂ) :
    0 ≤ finitePrimeMarginalVariation m := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem finitePrimeMarginalVariation_filter_le (m : Nat.Primes →₀ ℂ)
    (P : Nat.Primes → Prop) [DecidablePred P] :
    finitePrimeMarginalVariation (m.filter P) ≤ finitePrimeMarginalVariation m := by
  classical
  unfold finitePrimeMarginalVariation
  simp_rw [Finsupp.support_filter]
  calc
    _ = ∑ p ∈ m.support.filter P, ‖m p‖ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp hp).2]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => norm_nonneg _)

theorem finitePrimeMarginalEnergy_filter_eq_sum (c : Nat.Primes → ℝ)
    (m : Nat.Primes →₀ ℂ) (s : Finset Nat.Primes) :
    finitePrimeMarginalEnergy c (m.filter (fun p => p ∈ s)) =
      ∑ p ∈ s, (c p : ℂ) * m p := by
  classical
  rw [finitePrimeMarginalEnergy, Finsupp.sum_of_support_subset _
    (show (m.filter (fun p => p ∈ s)).support ⊆ s from
      fun p hp => (Finset.mem_filter.mp hp).2) _ (fun _ _ => mul_zero _)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finsupp.filter_apply_pos _ _ hp]

/-- Uniform variation turns coordinatewise vanishing into vanishing of every decaying reader. -/
theorem tendsto_finitePrimeMarginalEnergy_of_bounded_variation
    (c : Nat.Primes → ℝ) (hc : Tendsto c cofinite (nhds 0))
    (u : ℕ → Nat.Primes →₀ ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ n, finitePrimeMarginalVariation (u n) ≤ M)
    (hu : ∀ p, Tendsto (fun n => u n p) atTop (nhds 0)) :
    Tendsto (fun n => finitePrimeMarginalEnergy c (u n)) atTop (nhds 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (2 * (M + 1))
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) (by linarith))
  have hsmall : ∀ᶠ p in cofinite, |c p| < δ := by
    simpa [Real.dist_eq] using (Metric.tendsto_nhds.mp hc δ hδ)
  let s := (eventually_cofinite.mp hsmall).toFinset
  have hs : ∀ p, p ∉ s → |c p| ≤ δ := by
    intro p hp
    have hlt : |c p| < δ := by simpa [s] using hp
    exact hlt.le
  have hhead : Tendsto (fun n => finitePrimeMarginalEnergy c
      ((u n).filter (fun p => p ∈ s))) atTop (nhds 0) := by
    simp_rw [finitePrimeMarginalEnergy_filter_eq_sum]
    simpa using tendsto_finsetSum s (fun p _ => (hu p).const_mul (c p : ℂ))
  have hheadsmall := Metric.tendsto_nhds.mp hhead (ε / 2) (by positivity)
  filter_upwards [hheadsmall] with n hn
  have htail : ‖finitePrimeMarginalEnergy c ((u n).filter (fun p => p ∉ s))‖ ≤
      δ * M := by
    calc
      _ ≤ δ * finitePrimeMarginalVariation ((u n).filter (fun p => p ∉ s)) :=
        finitePrimeMarginalEnergy_norm_le _ _ _
          (fun p hp => hs p (Finset.mem_filter.mp hp).2)
      _ ≤ δ * finitePrimeMarginalVariation (u n) :=
        mul_le_mul_of_nonneg_left (finitePrimeMarginalVariation_filter_le _ _) hδ.le
      _ ≤ δ * M := mul_le_mul_of_nonneg_left (hbound n) hδ.le
  have hδM : δ * M < ε / 2 := by
    calc
      δ * M < δ * (M + 1) := mul_lt_mul_of_pos_left (by linarith) hδ
      _ = ε / 2 := by dsimp [δ]; field_simp
  have hsplit : finitePrimeMarginalEnergy c ((u n).filter (fun p => p ∈ s)) +
      finitePrimeMarginalEnergy c ((u n).filter (fun p => p ∉ s)) =
      finitePrimeMarginalEnergy c (u n) :=
    Finsupp.sum_filter_add_sum_filter_not (fun p => p ∈ s) (u n) (fun p z => (c p : ℂ) * z)
  rw [dist_zero_right, ← hsplit]
  have hn' : ‖finitePrimeMarginalEnergy c ((u n).filter (fun p => p ∈ s))‖ < ε / 2 := by
    simpa using hn
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem tendsto_primeReciprocal_cofinite (A : ℝ) :
    Tendsto (fun p : Nat.Primes => A / (p : ℕ)) cofinite (nhds 0) := by
  have hp : Tendsto (fun p : Nat.Primes => (p : ℝ)) cofinite atTop :=
    tendsto_natCast_atTop_atTop.comp
      (Nat.cofinite_eq_atTop ▸ (show Function.Injective (fun p : Nat.Primes => (p : ℕ)) from
        Subtype.val_injective).tendsto_cofinite)
  simpa [div_eq_mul_inv, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp hp).const_mul A

theorem finitePrimeMarginalVariation_sub_le (m v : Nat.Primes →₀ ℂ) :
    finitePrimeMarginalVariation (m - v) ≤
      finitePrimeMarginalVariation m + finitePrimeMarginalVariation v := by
  classical
  let s := m.support ∪ v.support
  have hmv : (m - v).support ⊆ s := Finsupp.support_sub
  have hs (w : Nat.Primes →₀ ℂ) (hw : w.support ⊆ s) :
      finitePrimeMarginalVariation w = ∑ p ∈ s, ‖w p‖ := by
    exact Finsupp.sum_of_support_subset w hw (fun _ z => ‖z‖) (fun _ _ => norm_zero)
  rw [hs _ hmv, hs _ Finset.subset_union_left, hs _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun p _ => norm_sub_le _ _

theorem finitePrimeMarginalEnergy_sub (c : Nat.Primes → ℝ) (m v : Nat.Primes →₀ ℂ) :
    finitePrimeMarginalEnergy c (m - v) =
      finitePrimeMarginalEnergy c m - finitePrimeMarginalEnergy c v := by
  exact Finsupp.sum_sub_index (fun _ _ _ => mul_sub _ _ _)

/-- Reader continuity at each finite target marginal under a uniform variation bound. -/
theorem tendsto_finitePrimeMarginalEnergy_of_marginals
    (c : Nat.Primes → ℝ) (hc : Tendsto c cofinite (nhds 0))
    (u : ℕ → Nat.Primes →₀ ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ n, finitePrimeMarginalVariation (u n) ≤ M)
    (m : Nat.Primes →₀ ℂ) (hu : ∀ p, Tendsto (fun n => u n p) atTop (nhds (m p))) :
    Tendsto (fun n => finitePrimeMarginalEnergy c (u n)) atTop
      (nhds (finitePrimeMarginalEnergy c m)) := by
  have hzero := tendsto_finitePrimeMarginalEnergy_of_bounded_variation c hc
    (fun n => u n - m) (M + finitePrimeMarginalVariation m)
    (add_nonneg hM (finitePrimeMarginalVariation_nonneg _))
    (fun n => (finitePrimeMarginalVariation_sub_le _ _).trans
      (add_le_add (hbound n) le_rfl))
    (fun p => by simpa using (hu p).sub_const (m p))
  have h := hzero.add_const (finitePrimeMarginalEnergy c m)
  simpa only [finitePrimeMarginalEnergy_sub, sub_add_cancel, zero_add] using h

/-- The continuity law applies to the existing literal prime-edge energy reporter. -/
theorem tendsto_primeLabelledEnergyReporter_of_marginals
    (A : ℝ) (u : ℕ → DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ n, finitePrimeMarginalVariation (deningerBigWittLeftPrimeMarginal (u n)) ≤ M)
    (m : Nat.Primes →₀ ℂ)
    (hu : ∀ p, Tendsto (fun n => deningerBigWittLeftPrimeMarginal (u n) p)
      atTop (nhds (m p))) :
    Tendsto (fun n => primeLabelledEnergyReporter (fun p => A / (p : ℕ)) (u n))
      atTop (nhds (finitePrimeMarginalEnergy (fun p => A / (p : ℕ)) m)) := by
  simp_rw [primeLabelledEnergyReporter_eq_marginal]
  exact tendsto_finitePrimeMarginalEnergy_of_marginals _ (tendsto_primeReciprocal_cofinite A)
    _ M hM hbound m hu

theorem finitePrimeMarginal_pair_difference_le_variation
    (m : Nat.Primes →₀ ℂ) (p q : Nat.Primes) :
    ‖m p - m q‖ ≤ finitePrimeMarginalVariation m := by
  classical
  by_cases hpq : p = q
  · simpa [hpq] using finitePrimeMarginalVariation_nonneg m
  let s := m.support ∪ {p, q}
  have hs : finitePrimeMarginalVariation m = ∑ r ∈ s, ‖m r‖ :=
    Finsupp.sum_of_support_subset m Finset.subset_union_left
      (fun _ z => ‖z‖) (fun _ _ => norm_zero)
  rw [hs]
  calc
    _ ≤ ‖m p‖ + ‖m q‖ := norm_sub_le _ _
    _ = ∑ r ∈ ({p, q} : Finset Nat.Primes), ‖m r‖ := by simp [hpq]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
      (fun _ _ _ => norm_nonneg _)

theorem deningerBigWittLeftPrimeMarginal_coherent_difference
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes)
    (hp : p ∈ s) (hq : q ∈ s) :
    deningerBigWittLeftPrimeMarginal (deningerBigWittCrossPairFiniteRightLegPacket a s) p -
      deningerBigWittLeftPrimeMarginal (deningerBigWittCrossPairFiniteRightLegPacket a s) q =
      (s.card : ℂ) * (starRingEnd ℂ) (a p - a q) := by
  rw [deningerBigWittLeftPrimeMarginal_coherent, if_pos hp,
    deningerBigWittLeftPrimeMarginal_coherent, if_pos hq, map_sub]
  ring

/-- Every retained profile difference forces variation proportional to the number of primes. -/
theorem deningerBigWittLeftPrimeMarginal_coherent_variation_lower
    (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes)
    (hp : p ∈ s) (hq : q ∈ s) :
    (s.card : ℝ) * ‖a p - a q‖ ≤
      finitePrimeMarginalVariation
        (deningerBigWittLeftPrimeMarginal (deningerBigWittCrossPairFiniteRightLegPacket a s)) := by
  have h := finitePrimeMarginal_pair_difference_le_variation
    (deningerBigWittLeftPrimeMarginal (deningerBigWittCrossPairFiniteRightLegPacket a s)) p q
  rw [deningerBigWittLeftPrimeMarginal_coherent_difference a s p q hp hq,
    norm_mul, Complex.norm_natCast, Complex.norm_conj] at h
  exact h

/-- Uniform variation on the complete unscaled coherent family is exactly profile constancy. -/
theorem deningerBigWittLeftPrimeMarginal_coherent_bounded_iff
    (a : Nat.Primes → ℂ) :
    (∃ M : ℝ, ∀ s : Finset Nat.Primes,
      finitePrimeMarginalVariation
        (deningerBigWittLeftPrimeMarginal (deningerBigWittCrossPairFiniteRightLegPacket a s)) ≤ M) ↔
      ∃ z : ℂ, ∀ p, a p = z := by
  classical
  constructor
  · rintro ⟨M, hM⟩
    let q := nthPrimeSubtype 0
    refine ⟨a q, fun p => ?_⟩
    by_contra hne
    have hd : 0 < ‖a p - a q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨N, hN⟩ := exists_nat_gt (M / ‖a p - a q‖)
    obtain ⟨t, ht⟩ := Infinite.exists_subset_card_eq Nat.Primes N
    let s := t ∪ {p, q}
    have hcard : (N : ℝ) ≤ s.card := by
      exact_mod_cast (ht ▸ Finset.card_le_card (Finset.subset_union_left : t ⊆ s))
    have hbound := (deningerBigWittLeftPrimeMarginal_coherent_variation_lower a s p q
      (by simp [s]) (by simp [s])).trans (hM s)
    have hlarge : M < (N : ℝ) * ‖a p - a q‖ := (div_lt_iff₀ hd).mp hN
    have := mul_le_mul_of_nonneg_right hcard hd.le
    linarith
  · rintro ⟨z, hz⟩
    refine ⟨0, fun s => ?_⟩
    have hm : deningerBigWittLeftPrimeMarginal
        (deningerBigWittCrossPairFiniteRightLegPacket a s) = 0 := by
      ext p
      rw [deningerBigWittLeftPrimeMarginal_coherent]
      simp [hz, nsmul_eq_mul]
    simp [hm, finitePrimeMarginalVariation]


/-- Scalar normalization commutes with the literal prime marginal. -/
theorem deningerBigWittLeftPrimeMarginal_smul
    (z : ℂ) (f : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) :
    deningerBigWittLeftPrimeMarginal (z • f) = z • deningerBigWittLeftPrimeMarginal f := by
  exact Finsupp.mapDomain_smul _ _

/-- The coherent variation cost retains the full scalar normalization. -/
theorem deningerBigWittLeftPrimeMarginal_coherent_smul_variation_lower
    (z : ℂ) (a : Nat.Primes → ℂ) (s : Finset Nat.Primes) (p q : Nat.Primes)
    (hp : p ∈ s) (hq : q ∈ s) :
    (s.card : ℝ) * ‖z * (a p - a q)‖ ≤
      finitePrimeMarginalVariation (deningerBigWittLeftPrimeMarginal
        (z • deningerBigWittCrossPairFiniteRightLegPacket a s)) := by
  have h := finitePrimeMarginal_pair_difference_le_variation
    (deningerBigWittLeftPrimeMarginal (z • deningerBigWittCrossPairFiniteRightLegPacket a s)) p q
  rw [deningerBigWittLeftPrimeMarginal_smul] at h
  simp only [Finsupp.smul_apply, smul_eq_mul, ← mul_sub] at h
  rw [deningerBigWittLeftPrimeMarginal_coherent_difference a s p q hp hq,
    norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_conj] at h
  rw [norm_mul, deningerBigWittLeftPrimeMarginal_smul]
  convert h using 1
  ring

/-- Uniform variation on growing complete coherent packets removes every fixed edge amplitude,
even with varying profiles and arbitrary complex scalar normalizations. The displayed difference
has the same norm as the literal conjugate right-leg coefficient. -/
theorem tendsto_normalized_coherent_edge_of_bounded_marginal_variation
    (z : ℕ → ℂ) (a : ℕ → Nat.Primes → ℂ) (s : ℕ → Finset Nat.Primes)
    (hcard : Tendsto (fun n => ((s n).card : ℝ)) atTop atTop)
    (p q : Nat.Primes) (hp : ∀ᶠ n in atTop, p ∈ s n) (hq : ∀ᶠ n in atTop, q ∈ s n)
    (M : ℝ) (hbound : ∀ n,
      finitePrimeMarginalVariation (deningerBigWittLeftPrimeMarginal
        (z n • deningerBigWittCrossPairFiniteRightLegPacket (a n) (s n))) ≤ M) :
    Tendsto (fun n => z n * (a n p - a n q)) atTop (nhds 0) := by
  have hlimit : Tendsto (fun n => M / ((s n).card : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hcard).const_mul M
  apply squeeze_zero_norm' _ hlimit
  filter_upwards [hp, hq, hcard.eventually (eventually_gt_atTop (0 : ℝ))] with n hpn hqn hn
  apply (le_div_iff₀ hn).mpr
  simpa only [mul_comm] using
    (deningerBigWittLeftPrimeMarginal_coherent_smul_variation_lower
      (z n) (a n) (s n) p q hpn hqn).trans (hbound n)
end
end RHTower.HedenmalmThetaSource
