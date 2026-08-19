import GaloisForLFunctions.RHTower.PrimeArchBernsteinMobiusPullbackSource
import GaloisForLFunctions.RHTower.PrimeArchBernsteinConfinedPhase

/-!
# The prime--archimedean moment pole--residue pinch law

The endpoint-normalized ordinary moment germ

```
M_R(v) = ∑_n (normalizedPrimeArchMoment n / R^n) v^n
```

is, near the origin, the reciprocal-coordinate resolvent `∑_q c_q/(1 - u_q v)` of the
multiplicity-indexed Xi divisor, with `c_q = xiZeroCopyReciprocalSquare q` and `u_q = c_q / R`.

Grouping the copies by their common normalized coordinate `u` gives `C_u = R u m_u` with `m_u` the
exact fibre multiplicity, so the poles are the simple points `p_u = 1/u` and the residue is exactly
`-R m_u`: no cancellation between multiplicity copies or reflection partners is possible.

The reflected Bernstein amplitude of the pole is `B(p) = (1+|p-1|)/|p|`, and triangle equality
gives `B(p) = 1` exactly on the ray `[1, ∞)`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The endpoint-normalized moment sequence `m_n = normalizedPrimeArchMoment(n)/R^n`. -/
def endpointMoment : ℕ → ℝ :=
  radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment

theorem xiEndpointNormalizedReciprocalSquare_mul (q : XiZeroCopy) :
    (primeArchEndpointHausdorffRadius : ℂ) * xiEndpointNormalizedReciprocalSquare q
      = xiZeroCopyReciprocalSquare q := by
  have hR : (primeArchEndpointHausdorffRadius : ℂ) ≠ 0 := by
    exact_mod_cast primeArchEndpointHausdorffRadius_pos.ne'
  rw [xiEndpointNormalizedReciprocalSquare]
  field_simp

/-- **(11)** The endpoint-normalized moments are the reciprocal-coordinate power sums. -/
theorem endpointMoment_eq_tsum (n : ℕ) :
    ((endpointMoment n : ℝ) : ℂ)
      = ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q
          * (xiEndpointNormalizedReciprocalSquare q) ^ n := by
  have hR : (primeArchEndpointHausdorffRadius : ℂ) ≠ 0 := by
    exact_mod_cast primeArchEndpointHausdorffRadius_pos.ne'
  have hterm : ∀ q : XiZeroCopy,
      xiZeroCopyReciprocalSquare q * (xiEndpointNormalizedReciprocalSquare q) ^ n
        = xiZeroCopyReciprocalSquare q ^ (n + 1) / (primeArchEndpointHausdorffRadius : ℂ) ^ n := by
    intro q
    rw [xiEndpointNormalizedReciprocalSquare, div_pow, pow_succ]
    field_simp
  rw [tsum_congr hterm, tsum_div_const, tsum_xiZeroCopyReciprocalSquare_pow n]
  rw [endpointMoment, radiusNormalizedMoment]
  push_cast
  rw [← primeArchSourceMoment_eq_xiCentralReciprocalMoment n]
  rw [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm]

/-- The reciprocal-coordinate resolvent `∑_q c_q / (1 - u_q v)`. -/
def endpointResolvent (v : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q
    / (1 - xiEndpointNormalizedReciprocalSquare q * v)

theorem exists_endpointNormalized_norm_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ q : XiZeroCopy, ‖xiEndpointNormalizedReciprocalSquare q‖ ≤ M := by
  obtain ⟨M, hM1, hM⟩ := exists_xiZeroCopyReciprocalSquare_norm_bound
  have hR := primeArchEndpointHausdorffRadius_pos
  refine ⟨M / primeArchEndpointHausdorffRadius, by positivity, fun q => ?_⟩
  rw [xiEndpointNormalizedReciprocalSquare, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hR]
  exact div_le_div_of_nonneg_right (hM q) hR.le

/-- **(2)** Near the origin the endpoint moment germ is the reciprocal-coordinate resolvent. -/
theorem bernsteinMomentGerm_endpoint_eq_resolvent {v : ℂ} {M : ℝ} (hM0 : 0 < M)
    (hM : ∀ q : XiZeroCopy, ‖xiEndpointNormalizedReciprocalSquare q‖ ≤ M)
    (hv : M * ‖v‖ < 1) :
    bernsteinMomentGerm endpointMoment v = endpointResolvent v := by
  set F : XiZeroCopy × ℕ → ℂ := fun p =>
    xiZeroCopyReciprocalSquare p.1 * (xiEndpointNormalizedReciprocalSquare p.1 * v) ^ p.2 with hF
  have hMv0 : 0 ≤ M * ‖v‖ := by positivity
  have hqv : ∀ q : XiZeroCopy, ‖xiEndpointNormalizedReciprocalSquare q * v‖ < 1 := by
    intro q
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hM q) (norm_nonneg v)) hv
  have hsum : Summable F := by
    refine Summable.of_norm_bounded (f := F) (g := fun p : XiZeroCopy × ℕ =>
      ‖xiZeroCopyReciprocalSquare p.1‖ * (M * ‖v‖) ^ p.2) ?_ ?_
    · exact Summable.mul_of_nonneg summable_xiZeroCopyReciprocalSquare.norm
        (summable_geometric_of_lt_one hMv0 hv) (fun _ => norm_nonneg _)
        (fun n => by positivity)
    · intro p
      have h1 : ‖xiEndpointNormalizedReciprocalSquare p.1 * v‖ ≤ M * ‖v‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM p.1) (norm_nonneg v)
      have h2 : ‖(xiEndpointNormalizedReciprocalSquare p.1 * v) ^ p.2‖ ≤ (M * ‖v‖) ^ p.2 := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg (xiEndpointNormalizedReciprocalSquare p.1 * v))
          h1 p.2
      calc ‖F p‖ = ‖xiZeroCopyReciprocalSquare p.1‖
            * ‖(xiEndpointNormalizedReciprocalSquare p.1 * v) ^ p.2‖ := by
            rw [hF]; simp only [norm_mul]
        _ ≤ ‖xiZeroCopyReciprocalSquare p.1‖ * (M * ‖v‖) ^ p.2 :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have hrow : ∀ q : XiZeroCopy, ∑' n : ℕ, F (q, n)
      = xiZeroCopyReciprocalSquare q
        / (1 - xiEndpointNormalizedReciprocalSquare q * v) := by
    intro q
    rw [hF]
    simp only
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (hqv q), div_eq_mul_inv]
  have hcol : ∀ n : ℕ, ∑' q : XiZeroCopy, F (q, n)
      = ((endpointMoment n : ℝ) : ℂ) * v ^ n := by
    intro n
    rw [hF]
    simp only
    rw [endpointMoment_eq_tsum n, ← tsum_mul_right]
    exact tsum_congr fun q => by rw [mul_pow]; ring
  have h1 : ∑' p : XiZeroCopy × ℕ, F p = endpointResolvent v := by
    rw [hsum.tsum_prod, endpointResolvent]
    exact tsum_congr hrow
  have hswap : Summable (fun p : ℕ × XiZeroCopy => F (p.2, p.1)) := by
    refine (((Equiv.prodComm ℕ XiZeroCopy).summable_iff (f := F)).mpr hsum).congr fun p => rfl
  have h2 : ∑' p : XiZeroCopy × ℕ, F p = bernsteinMomentGerm endpointMoment v := by
    have heq : ∑' p : XiZeroCopy × ℕ, F p = ∑' p : ℕ × XiZeroCopy, F (p.2, p.1) :=
      ((Equiv.prodComm ℕ XiZeroCopy).tsum_eq F).symm
    rw [heq, hswap.tsum_prod, bernsteinMomentGerm]
    exact tsum_congr hcol
  rw [← h2, h1]

/-! ### The exact pole set and residue quantization -/

theorem summable_xiEndpointNormalizedReciprocalSquare :
    Summable xiEndpointNormalizedReciprocalSquare := by
  have h := summable_xiZeroCopyReciprocalSquare.div_const
    ((primeArchEndpointHausdorffRadius : ℝ) : ℂ)
  exact h.congr fun q => by rw [xiEndpointNormalizedReciprocalSquare]

/-- The fibre of multiplicity copies with a given normalized coordinate. -/
def endpointFibre (u : ℂ) : Set XiZeroCopy :=
  {q | xiEndpointNormalizedReciprocalSquare q = u}

theorem reciprocalSquare_of_mem_fibre {u : ℂ} {q : XiZeroCopy} (hq : q ∈ endpointFibre u) :
    xiZeroCopyReciprocalSquare q = (primeArchEndpointHausdorffRadius : ℂ) * u := by
  rw [← xiEndpointNormalizedReciprocalSquare_mul q, hq]

/-- **(3)** A nonzero fibre is finite. -/
theorem finite_endpointFibre {u : ℂ} (hu : u ≠ 0) : (endpointFibre u).Finite := by
  have hR : (primeArchEndpointHausdorffRadius : ℂ) ≠ 0 := by
    exact_mod_cast primeArchEndpointHausdorffRadius_pos.ne'
  have hsub : Summable
      (fun q : endpointFibre u => xiZeroCopyReciprocalSquare (q : XiZeroCopy)) :=
    summable_xiZeroCopyReciprocalSquare.subtype _
  have hconst : Summable
      (fun _ : endpointFibre u => (primeArchEndpointHausdorffRadius : ℂ) * u) :=
    hsub.congr fun q => reciprocalSquare_of_mem_fibre q.2
  have hne : (primeArchEndpointHausdorffRadius : ℂ) * u ≠ 0 := mul_ne_zero hR hu
  by_contra hfin
  haveI : Infinite (endpointFibre u) := Set.infinite_coe_iff.mpr hfin
  exact hne ((summable_const_iff _).mp hconst)

theorem tsum_reciprocalSquare_fibre {u : ℂ} (hu : u ≠ 0) :
    ∑' q : endpointFibre u, xiZeroCopyReciprocalSquare (q : XiZeroCopy)
      = (Nat.card (endpointFibre u) : ℂ) * ((primeArchEndpointHausdorffRadius : ℂ) * u) := by
  haveI : Fintype (endpointFibre u) := (finite_endpointFibre hu).fintype
  rw [tsum_fintype]
  rw [Finset.sum_congr rfl (fun q _ => reciprocalSquare_of_mem_fibre q.2)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  rw [Nat.card_eq_fintype_card]

/-- The `q`-th resolvent term. -/
def resolventTerm (v : ℂ) (q : XiZeroCopy) : ℂ :=
  xiZeroCopyReciprocalSquare q / (1 - xiEndpointNormalizedReciprocalSquare q * v)

theorem endpointResolvent_eq_tsum (v : ℂ) :
    endpointResolvent v = ∑' q : XiZeroCopy, resolventTerm v q := rfl

theorem finite_largeCoordinate {ε : ℝ} (hε : 0 < ε) :
    {q : XiZeroCopy | ε < ‖xiEndpointNormalizedReciprocalSquare q‖}.Finite := by
  have h := summable_xiEndpointNormalizedReciprocalSquare.tendsto_cofinite_zero
  have hmem : {q : XiZeroCopy | ‖xiEndpointNormalizedReciprocalSquare q‖ < ε}
      ∈ Filter.cofinite := by
    have h2 := h (Metric.ball_mem_nhds (0 : ℂ) hε)
    simpa [Metric.mem_ball, dist_zero_right, Set.preimage] using h2
  have hfin : ({q : XiZeroCopy | ‖xiEndpointNormalizedReciprocalSquare q‖ < ε}ᶜ).Finite :=
    Filter.mem_cofinite.mp hmem
  refine hfin.subset fun q hq => ?_
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  exact le_of_lt hq

theorem norm_resolventTerm_le {ε : ℝ} {v : ℂ} (hv : ε * ‖v‖ ≤ 1 / 2)
    {q : XiZeroCopy} (hq : ‖xiEndpointNormalizedReciprocalSquare q‖ ≤ ε) :
    ‖resolventTerm v q‖ ≤ 2 * ‖xiZeroCopyReciprocalSquare q‖ := by
  have h1 : ‖xiEndpointNormalizedReciprocalSquare q * v‖ ≤ 1 / 2 := by
    rw [norm_mul]
    exact le_trans (mul_le_mul_of_nonneg_right hq (norm_nonneg v)) hv
  have h2 : (1 : ℝ) / 2 ≤ ‖1 - xiEndpointNormalizedReciprocalSquare q * v‖ := by
    have h3 := norm_sub_norm_le (1 : ℂ) (xiEndpointNormalizedReciprocalSquare q * v)
    rw [norm_one] at h3
    linarith
  rw [resolventTerm, norm_div, div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (xiZeroCopyReciprocalSquare q)]

theorem summable_resolventTerm_compl {ε : ℝ} {v : ℂ} (hv : ε * ‖v‖ ≤ 1 / 2)
    (S : Set XiZeroCopy)
    (hS : ∀ q : XiZeroCopy, q ∉ S → ‖xiEndpointNormalizedReciprocalSquare q‖ ≤ ε) :
    Summable (fun q : (Sᶜ : Set XiZeroCopy) => resolventTerm v (q : XiZeroCopy)) := by
  refine Summable.of_norm_bounded
    (g := fun q : (Sᶜ : Set XiZeroCopy) => 2 * ‖xiZeroCopyReciprocalSquare (q : XiZeroCopy)‖)
    ((summable_xiZeroCopyReciprocalSquare.norm.subtype _).mul_left 2) fun q => ?_
  exact norm_resolventTerm_le hv (hS q q.2)

theorem norm_tsum_resolventTerm_compl_le {ε : ℝ} {v : ℂ} (hv : ε * ‖v‖ ≤ 1 / 2)
    (S : Set XiZeroCopy)
    (hS : ∀ q : XiZeroCopy, q ∉ S → ‖xiEndpointNormalizedReciprocalSquare q‖ ≤ ε) :
    ‖∑' q : (Sᶜ : Set XiZeroCopy), resolventTerm v (q : XiZeroCopy)‖
      ≤ 2 * ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ := by
  refine le_trans (norm_tsum_le_tsum_norm (summable_resolventTerm_compl hv S hS).norm) ?_
  refine le_trans (Summable.tsum_le_tsum (fun q => norm_resolventTerm_le hv (hS q q.2))
    (summable_resolventTerm_compl hv S hS).norm
    ((summable_xiZeroCopyReciprocalSquare.norm.subtype _).mul_left 2)) ?_
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact (summable_xiZeroCopyReciprocalSquare.norm.subtype _).tsum_le_tsum_of_inj
    (fun q : (Sᶜ : Set XiZeroCopy) => (q : XiZeroCopy))
    (Subtype.val_injective) (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
    summable_xiZeroCopyReciprocalSquare.norm

/-- Splitting a summable family over a finite set and its complement. -/
theorem tsum_split_finite {α : Type*} {f : α → ℂ} {S : Set α} (hS : S.Finite)
    (hcompl : Summable (fun q : (Sᶜ : Set α) => f (q : α))) :
    ∑' q : α, f q = (∑ q ∈ hS.toFinset, f q) + ∑' q : (Sᶜ : Set α), f (q : α) := by
  classical
  haveI : Fintype S := hS.fintype
  have hS' : Summable (fun q : S => f (q : α)) := (hasSum_fintype _).summable
  have hsplit := hS'.tsum_add_tsum_compl hcompl
  rw [← hsplit]
  congr 1
  rw [tsum_subtype]
  rw [tsum_eq_sum (s := hS.toFinset) (fun q hq => by
    refine Set.indicator_of_notMem ?_ _
    rwa [Set.Finite.mem_toFinset] at hq)]
  refine Finset.sum_congr rfl fun q hq => ?_
  refine Set.indicator_of_mem ?_ _
  rwa [Set.Finite.mem_toFinset] at hq

set_option maxHeartbeats 1000000 in
/-- **(4)** The residue of the endpoint moment germ at the pole `1/u` is exactly `-R m_u`. -/
theorem tendsto_endpointResolvent_residue {u : ℂ} (hu : u ≠ 0) :
    Tendsto (fun v => (v - u⁻¹) * endpointResolvent v) (𝓝[≠] u⁻¹)
      (𝓝 (-((primeArchEndpointHausdorffRadius : ℂ)
        * ((endpointFibre u).ncard : ℂ)))) := by
  classical
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set p : ℂ := u⁻¹ with hp
  set ε : ℝ := min (‖u‖ / 2) (1 / (2 * (‖p‖ + 1))) with hεdef
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  have hε1 : ε ≤ ‖u‖ / 2 := min_le_left _ _
  have hε2 : ε ≤ 1 / (2 * (‖p‖ + 1)) := min_le_right _ _
  set S : Set XiZeroCopy := {q | ε < ‖xiEndpointNormalizedReciprocalSquare q‖} with hSdef
  have hSfin : S.Finite := finite_largeCoordinate hεpos
  have hScompl : ∀ q : XiZeroCopy, q ∉ S → ‖xiEndpointNormalizedReciprocalSquare q‖ ≤ ε := by
    intro q hq
    rw [hSdef, Set.mem_setOf_eq, not_lt] at hq
    exact hq
  have hfibS : endpointFibre u ⊆ S := by
    intro q hq
    rw [hSdef, Set.mem_setOf_eq, show xiEndpointNormalizedReciprocalSquare q = u from hq]
    linarith
  have hFfin : (endpointFibre u).Finite := finite_endpointFibre hu
  set Ffin : Finset XiZeroCopy := hFfin.toFinset with hFfindef
  set Sfin : Finset XiZeroCopy := hSfin.toFinset with hSfindef
  have hsub : Ffin ⊆ Sfin := by
    intro q hq
    rw [hSfindef, Set.Finite.mem_toFinset]
    exact hfibS (by rwa [hFfindef, Set.Finite.mem_toFinset] at hq)
  -- the decomposition of the resolvent on a punctured ball
  have hball : ∀ v : ℂ, ‖v - p‖ < 1 → ε * ‖v‖ ≤ 1 / 2 := by
    intro v hv
    have hvn : ‖v‖ ≤ ‖p‖ + 1 := by
      have := norm_add_le (v - p) p
      simp only [sub_add_cancel] at this
      linarith
    calc ε * ‖v‖ ≤ (1 / (2 * (‖p‖ + 1))) * (‖p‖ + 1) := by
          refine mul_le_mul hε2 hvn (norm_nonneg v) (by positivity)
      _ = 1 / 2 := by field_simp
  have hdecomp : ∀ v : ℂ, ‖v - p‖ < 1 →
      endpointResolvent v = (∑ q ∈ Ffin, resolventTerm v q)
        + (∑ q ∈ Sfin \ Ffin, resolventTerm v q)
        + (∑' q : (Sᶜ : Set XiZeroCopy), resolventTerm v (q : XiZeroCopy)) := by
    intro v hv
    have hcompl := summable_resolventTerm_compl (hball v hv) S hScompl
    rw [endpointResolvent_eq_tsum, tsum_split_finite hSfin hcompl, ← hSfindef,
      ← Finset.sum_sdiff hsub]
    ring
  -- the fibre part is exactly constant
  have hfibre : ∀ v : ℂ, v ≠ p →
      (v - p) * (∑ q ∈ Ffin, resolventTerm v q)
        = -((primeArchEndpointHausdorffRadius : ℂ) * ((endpointFibre u).ncard : ℂ)) := by
    intro v hvp
    have hden : (1 : ℂ) - u * v ≠ 0 := by
      intro hc
      have huv : u * v = 1 := by linear_combination -hc
      have hvu : v = u⁻¹ := by
        rw [inv_eq_one_div, eq_div_iff hu]
        linear_combination huv
      exact hvp (by rw [hp]; exact hvu)
    have hterm : ∀ q ∈ Ffin, resolventTerm v q
        = ((primeArchEndpointHausdorffRadius : ℂ) * u) / (1 - u * v) := by
      intro q hq
      rw [hFfindef, Set.Finite.mem_toFinset] at hq
      rw [resolventTerm, reciprocalSquare_of_mem_fibre hq,
        show xiEndpointNormalizedReciprocalSquare q = u from hq]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Ffin.card : ℂ) = ((endpointFibre u).ncard : ℂ) := by
      rw [hFfindef, Set.ncard_eq_toFinset_card (endpointFibre u) hFfin]
    rw [hcard, hp]
    field_simp
    ring
  -- the remaining finite part is continuous at the pole
  have hcont : ContinuousAt (fun v => ∑ q ∈ Sfin \ Ffin, resolventTerm v q) p := by
    refine continuousAt_finset_sum _ fun q hq => ?_
    have hqnot : q ∉ endpointFibre u := by
      intro hmem
      exact (Finset.mem_sdiff.mp hq).2 (by rw [hFfindef, Set.Finite.mem_toFinset]; exact hmem)
    have hne : xiEndpointNormalizedReciprocalSquare q ≠ u := hqnot
    have hden : (1 : ℂ) - xiEndpointNormalizedReciprocalSquare q * p ≠ 0 := by
      intro hc
      apply hne
      have h1 : xiEndpointNormalizedReciprocalSquare q * p = 1 := by linear_combination -hc
      rw [hp] at h1
      field_simp at h1
      exact h1
    refine ContinuousAt.div continuousAt_const ?_ hden
    exact continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hsubp : Tendsto (fun v : ℂ => v - p) (nhdsWithin p {p}ᶜ) (𝓝 0) := by
    have : Tendsto (fun v : ℂ => v - p) (𝓝 p) (𝓝 0) := by
      simpa using (continuous_id.sub continuous_const).tendsto p
    exact this.mono_left nhdsWithin_le_nhds
  have hzero1 : Tendsto (fun v => (v - p) * (∑ q ∈ Sfin \ Ffin, resolventTerm v q))
      (nhdsWithin p {p}ᶜ) (𝓝 0) := by
    have h2 : Tendsto (fun v => ∑ q ∈ Sfin \ Ffin, resolventTerm v q)
        (nhdsWithin p {p}ᶜ) (𝓝 (∑ q ∈ Sfin \ Ffin, resolventTerm p q)) :=
      hcont.continuousWithinAt
    simpa using hsubp.mul h2
  have hzero2 : Tendsto
      (fun v => (v - p) * (∑' q : (Sᶜ : Set XiZeroCopy), resolventTerm v (q : XiZeroCopy)))
      (nhdsWithin p {p}ᶜ) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds p (by norm_num : (0:ℝ) < 1))]
        with v hv
      have hvn : ‖v - p‖ < 1 := by
        rw [Metric.mem_ball, Complex.dist_eq] at hv
        exact hv
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_tsum_resolventTerm_compl_le (hball v hvn) S hScompl) (norm_nonneg _)
    · have : Tendsto (fun v : ℂ => ‖v - p‖ * (2 * ∑' q : XiZeroCopy,
          ‖xiZeroCopyReciprocalSquare q‖)) (nhdsWithin p {p}ᶜ) (𝓝 0) := by
        simpa using (hsubp.norm).mul_const (2 * ∑' q : XiZeroCopy,
          ‖xiZeroCopyReciprocalSquare q‖)
      exact this
  have hcongr : ∀ᶠ v in nhdsWithin p {p}ᶜ, (v - p) * endpointResolvent v
      = -((primeArchEndpointHausdorffRadius : ℂ) * ((endpointFibre u).ncard : ℂ))
        + ((v - p) * (∑ q ∈ Sfin \ Ffin, resolventTerm v q)
          + (v - p) * (∑' q : (Sᶜ : Set XiZeroCopy), resolventTerm v (q : XiZeroCopy))) := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds p (by norm_num : (0:ℝ) < 1)),
      self_mem_nhdsWithin] with v hv hvp
    have hvn : ‖v - p‖ < 1 := by
      rw [Metric.mem_ball, Complex.dist_eq] at hv
      exact hv
    have hvp' : v ≠ p := hvp
    rw [hdecomp v hvn, mul_add, mul_add, hfibre v hvp']
    ring
  refine Tendsto.congr' (EventuallyEq.symm hcongr) ?_
  simpa using (tendsto_const_nhds.add (hzero1.add hzero2))

end

end RHTower
