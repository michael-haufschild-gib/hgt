import GaloisForLFunctions.RHTower.ZetaSelfReturnThresholdIsTheDistanceToNonvanishingTargets
import GaloisForLFunctions.RHTower.ZetaDiscRecurrenceOnEveryClosedDiscOfTheStrip
import GaloisForLFunctions.RHTower.FiniteEulerProductKroneckerWeylLimitLaw

/-!
# Twisted Dirichlet heads near a zero have vanishing Haar mass

Attach a unimodular phase `ω(p)` to every prime and extend it completely multiplicatively:
`primePhaseTwist ω n = ∏_{p ∣ n} ω(p)^{v_p(n)}`.  The *twisted Dirichlet head* of length `M` is

  `twistedDirichletHead M ω z = Σ_{n ≤ M} primePhaseTwist ω n · n^{−z}`;

along the prime phase flow `ω = (p^{−iτ})_p` it is the plain head at `z + iτ`
(`twistedDirichletHead_circlePhaseFlow`), so the heights at which the head approximates `ζ` on a
disc `D` are the visits of the flow to the open set of phases
`twistedHeadPhaseSet M D ε = {ω : sup_D |twistedDirichletHead M ω − ζ| < ε}`
(`headTargetReturnSet_eq_preimage`, `isOpen_twistedHeadPhaseSet`).

Twisted heads are Dirichlet polynomials and may vanish, so Hurwitz's theorem does not keep them
away from a target with a zero.  Nevertheless, below the self-return threshold
`d = zetaNonvanishingDistance z₀ r` of the disc, the Haar mass of the approximating phases tends
to zero with the length of the head (`eventually_torusHaar_twistedHeadPhaseSet_le`): a set of
phases of Haar mass `> δ` would be visited by the flow at lower density `> δ`
(Kronecker–Weyl), the visits are self-returns of `ζ` within `ε + ε' < d` off the tail-bad
heights, the former have measure `≤ T^θ` and the latter have density `≤ δ/2` for long heads.
Above the threshold, in particular on every disc whose open part is zero-free, the
approximating phases are nonempty for all long heads
(`eventually_nonempty_twistedHeadPhaseSet_of_zeroFree`).  So the probability that a random
completely multiplicative twist of the Dirichlet head of length `M` reproduces `ζ` on a disc
around an off-line zero vanishes as `M → ∞`, although nothing forbids individual twists from
doing so.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## 1. Completely multiplicative phases -/

/-- The phase of `n` under prime phases `ω`: the completely multiplicative extension
`∏_{p ∣ n} ω(p)^{v_p(n)}`. -/
def primePhaseTwist (ω : Nat.Primes → Circle) (n : ℕ) : ℂ :=
  ∏ p ∈ n.primeFactors, (if hp : p.Prime then (ω ⟨p, hp⟩ : ℂ) else 1) ^ n.factorization p

theorem continuous_primePhaseTwist (n : ℕ) :
    Continuous fun ω : Nat.Primes → Circle => primePhaseTwist ω n := by
  unfold primePhaseTwist
  refine continuous_finsetProd _ fun p _ => ?_
  by_cases hp : p.Prime
  · simp only [dif_pos hp]
    exact (continuous_subtype_val.comp (continuous_apply (⟨p, hp⟩ : Nat.Primes))).pow _
  · simp only [dif_neg hp]
    exact continuous_const

theorem norm_primePhaseTwist (ω : Nat.Primes → Circle) (n : ℕ) : ‖primePhaseTwist ω n‖ = 1 := by
  unfold primePhaseTwist
  rw [norm_prod]
  refine Finset.prod_eq_one fun p hp => ?_
  rw [norm_pow, dif_pos (Nat.prime_of_mem_primeFactors hp), Circle.norm_coe, one_pow]

/-- `log n = Σ_{p ∣ n} v_p(n) log p`. -/
theorem log_natCast_eq_sum_factorization_mul_log {n : ℕ} (hn : n ≠ 0) :
    Real.log n = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod, Real.log_prod]
  · exact Finset.sum_congr rfl fun p _ => by rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).pos
    positivity

/-- Along the prime phase flow the twist of `n` is `n^{−iτ}`. -/
theorem primePhaseTwist_circlePhaseFlow (τ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    primePhaseTwist (circlePhaseFlow primeFrequency τ) n = ((n : ℝ) : ℂ) ^ (-(τ * I)) := by
  have hn0 : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.ofReal_natCast, ← Complex.natCast_log,
    log_natCast_eq_sum_factorization_mul_log hn]
  push_cast
  rw [Finset.sum_mul, Complex.exp_sum]
  unfold primePhaseTwist
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [dif_pos (Nat.prime_of_mem_primeFactors hp), HTGeometry.circlePhaseFlow_coe,
    ← Complex.exp_nat_mul]
  congr 1
  simp only [primeFrequency]
  push_cast
  ring

/-! ## 2. Twisted heads and the phase flow -/

/-- The Dirichlet head of length `M` twisted by the prime phases `ω`. -/
def twistedDirichletHead (M : ℕ) (ω : Nat.Primes → Circle) (z : ℂ) : ℂ :=
  edPoly (primePhaseTwist ω) (Finset.Icc 1 M) z

/-- Along the prime phase flow the twisted head at `z` is the plain head at `z + iτ`. -/
theorem twistedDirichletHead_circlePhaseFlow (M : ℕ) (τ : ℝ) (z : ℂ) :
    twistedDirichletHead M (circlePhaseFlow primeFrequency τ) z
      = edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) := by
  unfold twistedDirichletHead edPoly
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  have hn0' : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0
  rw [primePhaseTwist_circlePhaseFlow τ hn0, one_mul, neg_add, Complex.cpow_add _ _ hn0', mul_comm]

/-- The twisted head is jointly continuous in the phases and the point. -/
theorem continuous_twistedDirichletHead_prod (M : ℕ) :
    Continuous fun q : (Nat.Primes → Circle) × ℂ => twistedDirichletHead M q.1 q.2 := by
  unfold twistedDirichletHead edPoly
  refine continuous_finsetSum _ fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  refine ((continuous_primePhaseTwist n).comp continuous_fst).mul ?_
  refine continuous_const.cpow (continuous_neg.comp continuous_snd) fun _ => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (Nat.cast_pos.mpr (by omega))

/-- The prime phases under which the twisted head of length `M` is within `ε` of `ζ` on `K`. -/
def twistedHeadPhaseSet (M : ℕ) (K : Set ℂ) (ε : ℝ) : Set (Nat.Primes → Circle) :=
  {ω | ∀ z ∈ K, ‖twistedDirichletHead M ω z - riemannZeta z‖ < ε}

/-- Head-target heights are the visits of the prime phase flow to the approximating phases. -/
theorem headTargetReturnSet_eq_preimage (M : ℕ) (K : Set ℂ) (ε : ℝ) :
    headTargetReturnSet M K ε = circlePhaseFlow primeFrequency ⁻¹' twistedHeadPhaseSet M K ε := by
  ext τ
  simp only [headTargetReturnSet, twistedHeadPhaseSet, mem_setOf_eq, mem_preimage,
    twistedDirichletHead_circlePhaseFlow]

/-- For a compact `K` avoiding the pole, the approximating phases form an open set. -/
theorem isOpen_twistedHeadPhaseSet (M : ℕ) {K : Set ℂ} (hK : IsCompact K)
    (hre : ∀ z ∈ K, z ≠ 1) (ε : ℝ) : IsOpen (twistedHeadPhaseSet M K ε) := by
  rw [isOpen_iff_eventually]
  intro ω₀ hω₀
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hζ : ContinuousOn riemannZeta K := fun z hz =>
    (differentiableAt_riemannZeta (hre z hz)).continuousAt.continuousWithinAt
  have hΦ : Continuous
      (fun q : (Nat.Primes → Circle) × K => ‖twistedDirichletHead M q.1 q.2 - riemannZeta q.2‖) :=
    (((continuous_twistedDirichletHead_prod M).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).sub
      ((continuousOn_iff_continuous_restrict.mp hζ).comp continuous_snd)).norm
  have h := (isCompact_univ (X := K)).eventually_forall_of_forall_eventually (x₀ := ω₀)
    (P := fun ω (z : K) => ‖twistedDirichletHead M ω z - riemannZeta z‖ < ε)
    (fun z _ => (hΦ.tendsto (ω₀, z)).eventually (eventually_lt_nhds (hω₀ z z.2)))
  exact h.mono fun ω hω z hz => hω ⟨z, hz⟩ (mem_univ _)

/-! ## 3. Vanishing Haar mass below the threshold -/

/-- Points of a closed disc left of `Re s = 1` are not the pole. -/
theorem ne_one_of_mem_closedBall_of_lt {z₀ : ℂ} {r : ℝ} (h1 : z₀.re + r < 1) {z : ℂ}
    (hz : z ∈ closedBall z₀ r) : z ≠ 1 := by
  intro h
  have := (abs_le.mp ((abs_re_le_norm (z - z₀)).trans (mem_closedBall_iff_norm.mp hz))).2
  rw [sub_re, h, one_re] at this
  linarith

/-- **Twisted heads near a zero have vanishing Haar mass.**  On a disc with doubled closure in
the strip and `ε` below the self-return threshold, for every `δ > 0` and all long heads the
approximating phases have Haar mass at most `δ`. -/
theorem eventually_torusHaar_twistedHeadPhaseSet_le {z₀ : ℂ} {r ε : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < z₀.re - 2 * r) (h1 : z₀.re + 2 * r < 1)
    (hε : ε < zetaNonvanishingDistance z₀ r) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop,
      (torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹'
        twistedHeadPhaseSet M (closedBall z₀ r) ε)).toReal ≤ δ := by
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = (zetaNonvanishingDistance z₀ r - ε) / 2 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; linarith
  have hsum : ε' + ε < zetaNonvanishingDistance z₀ r := by rw [hε']; linarith
  obtain ⟨θ, hθ, T₀, hT₀⟩ := exists_volume_zetaReturnSet_le_rpow_of_lt_distance hr
    (by linarith) (by linarith) hsum
  filter_upwards [eventually_eventually_volume_discTailBadSet_le_of_lt (show r < 2 * r by linarith)
    h0 h1 hε'0 (half_pos hδ)] with M hM
  by_contra hcon
  push Not at hcon
  have hvisit := eventually_ofReal_mul_le_volume_preimage_primeFlow
    (isOpen_twistedHeadPhaseSet M (isCompact_closedBall z₀ r)
      (fun z hz => ne_one_of_mem_closedBall_of_lt (by linarith) hz) ε) hcon
  rw [← headTargetReturnSet_eq_preimage] at hvisit
  have hsub : headTargetReturnSet M (closedBall z₀ r) ε ⊆
      discTailBadSet M z₀ r ε' ∪ zetaReturnSet (closedBall z₀ r) (ε' + ε) := by
    intro τ hτ
    by_cases hb : τ ∈ discTailBadSet M z₀ r ε'
    · exact Or.inl hb
    · exact Or.inr
        (headTargetReturnSet_diff_discTailBadSet_subset_zetaReturnSet M z₀ r ε ε' ⟨hτ, hb⟩)
  obtain ⟨T, hT1, hT2, hT3, hT4, hT5⟩ := (hvisit.and (hM.and ((eventually_ge_atTop T₀).and
    ((eventually_rpow_lt_const_mul_atTop hθ (half_pos hδ)).and (eventually_ge_atTop 0))))).exists
  have hle : volume (headTargetReturnSet M (closedBall z₀ r) ε ∩ Icc 0 T) ≤
      ENNReal.ofReal (δ / 2 * T) + ENNReal.ofReal (T ^ θ) := by
    calc volume (headTargetReturnSet M (closedBall z₀ r) ε ∩ Icc 0 T)
        ≤ volume (discTailBadSet M z₀ r ε' ∩ Icc 0 T ∪
            zetaReturnSet (closedBall z₀ r) (ε' + ε) ∩ Icc 0 T) := by
          refine measure_mono ?_
          rw [← Set.union_inter_distrib_right]
          exact inter_subset_inter_left _ hsub
      _ ≤ _ := (measure_union_le _ _).trans (add_le_add hT2 (hT₀ T hT3))
  have h := hT1.trans hle
  have hTθ : 0 ≤ T ^ θ := Real.rpow_nonneg hT5 θ
  rw [← ENNReal.ofReal_add (by positivity) hTθ,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  linarith

/-! ## 4. Nonempty approximating phases off the zeros -/

/-- **Zero-free discs admit approximating twists of every long head.**  If `ζ` has no zero in
the open disc, then for every `ε > 0` and all long heads some choice of prime phases brings the
twisted head within `ε` of `ζ` on the closed disc. -/
theorem eventually_nonempty_twistedHeadPhaseSet_of_zeroFree {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < z₀.re - 2 * r) (h1 : z₀.re + 2 * r < 1)
    (hζ : ∀ z ∈ ball z₀ r, riemannZeta z ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, (twistedHeadPhaseSet M (closedBall z₀ r) ε).Nonempty := by
  have hrec : ZetaDiscStronglyRecurrentOn (closedBall z₀ r) :=
    (zetaDiscStronglyRecurrentOn_iff_forall_ball_ne_zero hr h0 h1).mpr hζ
  have hdense := headTargetUniformlyDense_of_zetaDiscStronglyRecurrentOn_of_lt
    (show r < 2 * r by linarith) h0 h1 hrec
  obtain ⟨c, hc, hM⟩ := hdense ε hε
  filter_upwards [hM] with M hT
  obtain ⟨T, hT1, hT2⟩ := (hT.and (eventually_gt_atTop 0)).exists
  have hpos : volume (headTargetReturnSet M (closedBall z₀ r) ε ∩ Icc 0 T) ≠ 0 := by
    intro h
    rw [h] at hT1
    have : (0 : ℝ) < c * T := by positivity
    exact absurd hT1 (not_le.mpr (ENNReal.ofReal_pos.mpr this))
  obtain ⟨τ, hτ, -⟩ := nonempty_of_measure_ne_zero hpos
  rw [headTargetReturnSet_eq_preimage] at hτ
  exact ⟨_, hτ⟩

/-- **Around an off-line zero the Haar mass of the approximating twists vanishes.** -/
theorem exists_eventually_torusHaar_twistedHeadPhaseSet_le_of_zero {z₀ : ℂ}
    (hz : riemannZeta z₀ = 0) (h1 : 1 / 2 < z₀.re) (h2 : z₀.re < 1) :
    ∃ r > 0, (1 / 2 < z₀.re - 2 * r ∧ z₀.re + 2 * r < 1) ∧ ∃ ε > 0, ∀ δ > 0,
      ∀ᶠ M : ℕ in atTop,
        (torusHaar Nat.Primes (unitTorusHomeomorphCircles Nat.Primes ⁻¹'
          twistedHeadPhaseSet M (closedBall z₀ r) ε)).toReal ≤ δ := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = min ((z₀.re - 1 / 2) / 4) ((1 - z₀.re) / 4) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact lt_min (by linarith) (by linarith)
  have hr1 : r ≤ (z₀.re - 1 / 2) / 4 := by rw [hr]; exact min_le_left _ _
  have hr2 : r ≤ (1 - z₀.re) / 4 := by rw [hr]; exact min_le_right _ _
  have h0 : 1 / 2 < z₀.re - 2 * r := by linarith
  have h1' : z₀.re + 2 * r < 1 := by linarith
  have hd := zetaNonvanishingDistance_pos_of_zero hr0 (by linarith) (by linarith)
    (mem_ball_self hr0) hz
  exact ⟨r, hr0, ⟨h0, h1'⟩, _, half_pos hd, fun δ hδ =>
    eventually_torusHaar_twistedHeadPhaseSet_le hr0 h0 h1' (half_lt_self hd) hδ⟩

end

end RHTower
