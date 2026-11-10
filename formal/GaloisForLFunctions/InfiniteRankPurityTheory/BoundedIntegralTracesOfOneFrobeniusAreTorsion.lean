import GaloisForLFunctions.InfiniteRankPurityTheory.CesaroMeansReadTheModesOfASummableTower

/-!
# Bounded integral traces of one Frobenius are torsion

Kronecker's theorem says that an algebraic integer whose conjugates all lie in the closed unit disc is
zero or a root of unity. Its trace form: a finite family of numbers in the closed disc whose power
sums are integers consists of roots of unity and zeros. Here the family is infinite.

**Theorem** (`kronecker_oneFrobenius`, `kronecker_oneFrobenius_injective`). Let `(z_i, c_i)` be a
summable tower with all modes in the closed unit disc, of any rank, whose level sums
`S(ν) = Σ c_i z_i^ν` are integers for all large `ν`. Then there is one `τ ≥ 1` such that every point of
the unit circle carrying weight is a `τ`-th root of unity, and the level sums of the inner modes vanish
for all large `ν`. If the modes are distinct and their moduli have no infinite ascending chain, the
tower has finite rank: only finitely many modes are visible, and they are `τ`-th roots of unity.

**Proof.** Split `S = U + I` into the unimodular and the inner part.
- `I(ν) → 0` by dominated convergence.
- `U` has arbitrarily large almost periods, so `U(ν)` is a limit of the integers `S(ν + τ)`; hence
  `U(ν) ∈ ℤ`.
- An almost period of precision `½` of an integer sequence is a period: `U(ν + τ) = U(ν)`.
- The tower with weights `c_i (z_i^τ − 1)` has level sums zero, so by Cesàro means the weight at each
  point `w` of the circle times `w^τ − 1` vanishes.
- `I = S − U` is integer-valued and tends to zero, so it vanishes eventually; the largest visible
  inner radius would then carry weight zero by the same Cesàro argument.

Integrality and contraction leave no room for infinite rank in trace class: a pure trace-integral
module of weight zero and infinite rank cannot have summable weights.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*}

/-! ### Integers in `ℂ` -/

theorem int_eq_of_norm_sub_lt_one {m n : ℤ} (h : ‖(m : ℂ) - n‖ < 1) : m = n := by
  have h1 : ‖((m - n : ℤ) : ℂ)‖ < 1 := by
    push_cast
    exact h
  rw [Complex.norm_intCast] at h1
  have h2 : |m - n| < 1 := by exact_mod_cast h1
  have := Int.abs_lt_one_iff.mp h2
  omega

/-- A complex number within every `ε > 0` of an integer is an integer. -/
theorem exists_int_eq_of_forall_near {x : ℂ} (h : ∀ ε > 0, ∃ n : ℤ, ‖x - n‖ ≤ ε) :
    ∃ n : ℤ, x = n := by
  obtain ⟨n₀, hn₀⟩ := h (1 / 4) (by norm_num)
  refine ⟨n₀, ?_⟩
  have key : ∀ ε > 0, ε ≤ 1 / 4 → ‖x - n₀‖ ≤ ε := by
    intro ε hε hε4
    obtain ⟨n, hn⟩ := h ε hε
    have hnn : ‖(n : ℂ) - n₀‖ < 1 := by
      calc ‖(n : ℂ) - n₀‖ = ‖(x - n₀) - (x - n)‖ := by ring_nf
        _ ≤ ‖x - n₀‖ + ‖x - n‖ := norm_sub_le _ _
        _ ≤ 1 / 4 + ε := add_le_add hn₀ hn
        _ < 1 := by linarith
    rw [← int_eq_of_norm_sub_lt_one hnn]
    exact hn
  have h0 : ‖x - n₀‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := key (min ε (1 / 4)) (lt_min hε (by norm_num)) (min_le_right _ _)
    linarith [min_le_left ε (1 / 4)]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

/-! ### The unimodular and the inner part -/

/-- The weights of the modes on the unit circle. -/
noncomputable def circleWeight (c z : ι → ℂ) (i : ι) : ℂ := if ‖z i‖ = 1 then c i else 0

/-- The modes on the unit circle; the other modes are replaced by `1` and carry weight zero. -/
noncomputable def circleMode (z : ι → ℂ) (i : ι) : ℂ := if ‖z i‖ = 1 then z i else 1

/-- The weights of the modes off the unit circle. -/
noncomputable def innerWeight (c z : ι → ℂ) (i : ι) : ℂ := if ‖z i‖ = 1 then 0 else c i

theorem norm_circleMode (z : ι → ℂ) (i : ι) : ‖circleMode z i‖ = 1 := by
  unfold circleMode
  split_ifs with h
  · exact h
  · exact norm_one

theorem norm_circleWeight_le (c z : ι → ℂ) (i : ι) : ‖circleWeight c z i‖ ≤ ‖c i‖ := by
  unfold circleWeight
  split_ifs <;> simp

theorem norm_innerWeight_le (c z : ι → ℂ) (i : ι) : ‖innerWeight c z i‖ ≤ ‖c i‖ := by
  unfold innerWeight
  split_ifs <;> simp

theorem summable_circleWeight {c : ι → ℂ} (z : ι → ℂ) (hc : Summable fun i => ‖c i‖) :
    Summable fun i => ‖circleWeight c z i‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_circleWeight_le c z) hc

theorem summable_innerWeight {c : ι → ℂ} (z : ι → ℂ) (hc : Summable fun i => ‖c i‖) :
    Summable fun i => ‖innerWeight c z i‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_innerWeight_le c z) hc

/-- `S = U + I`. -/
theorem towerSum_eq_circle_add_inner {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ ≤ 1) (ν : ℕ) :
    towerSum c z ν =
      towerSum (circleWeight c z) (circleMode z) ν + towerSum (innerWeight c z) z ν := by
  rw [towerSum, towerSum, towerSum,
    ← (summable_towerTerm (summable_circleWeight z hc) (fun i => (norm_circleMode z i).le) ν).tsum_add
      (summable_towerTerm (summable_innerWeight z hc) hz ν)]
  refine tsum_congr fun i => ?_
  unfold circleWeight circleMode innerWeight
  split_ifs <;> simp

/-- The inner part tends to zero. -/
theorem tendsto_towerSum_inner {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ ≤ 1) : Tendsto (towerSum (innerWeight c z) z) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (ν : ℕ) (i : ι) => innerWeight c z i * z i ^ ν) (g := fun _ => (0 : ℂ))
    (bound := fun i => ‖c i‖) hc ?_ ?_
  · have e : towerSum (innerWeight c z) z =
        fun ν : ℕ => ∑' i, innerWeight c z i * z i ^ ν := rfl
    rw [e]
    simpa using h
  · intro i
    by_cases h1 : ‖z i‖ = 1
    · simp [innerWeight, h1]
    · have hlt : ‖z i‖ < 1 := lt_of_le_of_ne (hz i) h1
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt).const_mul (innerWeight c z i)
  · refine Eventually.of_forall fun ν i => ?_
    exact (norm_towerTerm_le hz ν i).trans (norm_innerWeight_le c z i)

/-- The weight at a point of the circle is read from the circle part. -/
theorem circle_merged_eq (c z : ι → ℂ) {w : ℂ} (hw : ‖w‖ = 1) (i : ι) :
    (if circleMode z i = w then circleWeight c z i else 0) = if z i = w then c i else 0 := by
  unfold circleMode circleWeight
  by_cases h1 : ‖z i‖ = 1
  · simp [h1]
  · have hne : z i ≠ w := fun h => h1 (by rw [h, hw])
    simp [h1, hne]

/-! ### Kronecker's theorem for a summable tower -/

/-- **Kronecker's theorem for one Frobenius at infinite rank.** A summable tower in the closed unit
disc with integer level sums at all large levels: one `τ ≥ 1` makes every point of the unit circle
that carries weight a `τ`-th root of unity, and the level sums of the inner modes vanish
eventually. -/
theorem kronecker_oneFrobenius {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hint : ∀ᶠ ν : ℕ in atTop, ∃ n : ℤ, towerSum c z ν = n) :
    ∃ τ : ℕ, 1 ≤ τ ∧
      (∀ w : ℂ, ‖w‖ = 1 → (∑' i, if z i = w then c i else 0) ≠ 0 → w ^ τ = 1) ∧
      ∀ᶠ ν : ℕ in atTop, towerSum (innerWeight c z) z ν = 0 := by
  set cu := circleWeight c z with hcu
  set zu := circleMode z with hzu
  set ci := innerWeight c z with hci
  have hcus : Summable fun i => ‖cu i‖ := summable_circleWeight z hc
  have hzu1 : ∀ i, ‖zu i‖ = 1 := norm_circleMode z
  have hsplit : ∀ ν, towerSum c z ν = towerSum cu zu ν + towerSum ci z ν :=
    towerSum_eq_circle_add_inner hc hz
  have hI : Tendsto (towerSum ci z) atTop (𝓝 0) := tendsto_towerSum_inner hc hz
  obtain ⟨ν₁, hν₁⟩ := eventually_atTop.mp hint
  -- the unimodular part is integer-valued
  have hUint : ∀ ν : ℕ, ∃ n : ℤ, towerSum cu zu ν = n := by
    intro ν
    refine exists_int_eq_of_forall_near fun ε hε => ?_
    have hε2 : 0 < ε / 2 := by positivity
    have hIev : ∀ᶠ μ : ℕ in atTop, ‖towerSum ci z μ‖ < ε / 2 := by
      have := (tendsto_zero_iff_norm_tendsto_zero.mp hI).eventually (gt_mem_nhds hε2)
      exact this
    obtain ⟨ν₂, hν₂⟩ := eventually_atTop.mp hIev
    obtain ⟨τ, hτT, -, hτ⟩ := exists_almostPeriod hcus hzu1 hε2 (max ν₁ ν₂)
    obtain ⟨n, hn⟩ := hν₁ (ν + τ) (by
      have := le_max_left ν₁ ν₂
      omega)
    refine ⟨n, ?_⟩
    have hIsmall := hν₂ (ν + τ) (by
      have := le_max_right ν₁ ν₂
      omega)
    have e : towerSum cu zu ν - n =
        -(towerSum cu zu (ν + τ) - towerSum cu zu ν) - towerSum ci z (ν + τ) := by
      rw [← hn, hsplit (ν + τ)]
      ring
    rw [e]
    calc ‖-(towerSum cu zu (ν + τ) - towerSum cu zu ν) - towerSum ci z (ν + τ)‖
        ≤ ‖-(towerSum cu zu (ν + τ) - towerSum cu zu ν)‖ + ‖towerSum ci z (ν + τ)‖ :=
          norm_sub_le _ _
      _ ≤ ε / 2 + ε / 2 := by
          rw [norm_neg]
          exact add_le_add (hτ ν) hIsmall.le
      _ = ε := by ring
  -- an almost period of precision ½ is a period
  obtain ⟨τ, -, hτ1, hτ⟩ := exists_almostPeriod hcus hzu1 (by norm_num : (0 : ℝ) < 1 / 2) 0
  have hper : ∀ ν : ℕ, towerSum cu zu (ν + τ) = towerSum cu zu ν := by
    intro ν
    obtain ⟨m, hm⟩ := hUint (ν + τ)
    obtain ⟨n, hn⟩ := hUint ν
    have hlt : ‖(m : ℂ) - n‖ < 1 := by
      rw [← hm, ← hn]
      exact (hτ ν).trans_lt (by norm_num)
    rw [hm, hn, int_eq_of_norm_sub_lt_one hlt]
  refine ⟨τ, hτ1, ?_, ?_⟩
  · -- the tower with weights `c (z^τ − 1)` has level sums zero
    intro w hw hmerged
    set c' : ι → ℂ := fun i => cu i * (zu i ^ τ - 1) with hc'
    have hc's : Summable fun i => ‖c' i‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) (hcus.mul_right 2)
      rw [hc']
      simp only [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖zu i ^ τ - 1‖ ≤ ‖zu i ^ τ‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hzu1 i, one_pow, norm_one]; norm_num
    have hzero : ∀ ν, towerSum c' zu ν = 0 := by
      intro ν
      have : towerSum c' zu ν = towerSum cu zu (ν + τ) - towerSum cu zu ν := by
        rw [towerSum, towerSum, towerSum,
          ← (summable_towerTerm hcus (fun i => (hzu1 i).le) _).tsum_sub
            (summable_towerTerm hcus (fun i => (hzu1 i).le) _)]
        refine tsum_congr fun i => ?_
        rw [hc', pow_add]
        ring
      rw [this, hper ν, sub_self]
    have h0 : Tendsto (towerSum c' zu) atTop (𝓝 0) := by
      have : towerSum c' zu = fun _ => 0 := funext hzero
      rw [this]
      exact tendsto_const_nhds
    have hm := merged_eq_zero_of_tendsto_zero hc's (fun i => (hzu1 i).le) h0 hw
    have hfac : (∑' i, if zu i = w then c' i else 0) =
        (w ^ τ - 1) * ∑' i, if z i = w then c i else 0 := by
      have key : ∀ i, (if zu i = w then c' i else 0) =
          (w ^ τ - 1) * (if zu i = w then cu i else 0) := by
        intro i
        by_cases h : zu i = w
        · rw [if_pos h, if_pos h, hc']
          simp only
          rw [h]
          ring
        · rw [if_neg h, if_neg h, mul_zero]
      rw [tsum_congr key, tsum_mul_left]
      congr 1
      exact tsum_congr (circle_merged_eq c z hw)
    rw [hfac] at hm
    rcases mul_eq_zero.mp hm with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hmerged
  · -- the inner part is integer-valued and tends to zero
    have hsmall : ∀ᶠ ν : ℕ in atTop, ‖towerSum ci z ν‖ < 1 :=
      (tendsto_zero_iff_norm_tendsto_zero.mp hI).eventually (gt_mem_nhds one_pos)
    filter_upwards [hsmall, eventually_ge_atTop ν₁] with ν hν hge
    obtain ⟨n, hn⟩ := hν₁ ν hge
    obtain ⟨m, hm⟩ := hUint ν
    have hval : towerSum ci z ν = ((n - m : ℤ) : ℂ) := by
      push_cast
      rw [← hn, ← hm, hsplit ν]
      ring
    have h0 : n - m = 0 := by
      have h1 : ‖((n - m : ℤ) : ℂ) - ((0 : ℤ) : ℂ)‖ < 1 := by
        rw [← hval]
        simpa using hν
      exact int_eq_of_norm_sub_lt_one h1
    rw [hval, h0]
    simp

/-- **Inner modes are invisible.** If the modes are distinct, their moduli have no infinite ascending
chain, and the inner level sums vanish eventually, then every inner mode other than `0` has weight
zero. -/
theorem inner_weight_eq_zero {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hinj : Function.Injective z)
    (hacc : ∀ S : Set ℝ, S ⊆ Set.range (fun i => ‖z i‖) → S.Nonempty → ∃ r ∈ S, ∀ t ∈ S, t ≤ r)
    (hI : ∀ᶠ ν : ℕ in atTop, towerSum (innerWeight c z) z ν = 0) :
    ∀ i, ‖z i‖ ≠ 1 → z i ≠ 0 → c i = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  -- the visible inner radii
  set S : Set ℝ := {r | ∃ i, ‖z i‖ = r ∧ ‖z i‖ ≠ 1 ∧ z i ≠ 0 ∧ c i ≠ 0} with hS
  have hSsub : S ⊆ Set.range (fun i => ‖z i‖) := by
    rintro r ⟨i, hi, -⟩
    exact ⟨i, hi⟩
  have hSne : S.Nonempty := by
    obtain ⟨i, h1, h2, h3⟩ := hcon
    exact ⟨‖z i‖, i, rfl, h1, h2, h3⟩
  obtain ⟨r, ⟨i₀, hi₀r, hi₀1, hi₀0, hi₀c⟩, hmax⟩ := hacc S hSsub hSne
  have hr0 : 0 < r := by
    rw [← hi₀r]
    exact norm_pos_iff.mpr hi₀0
  have hr1 : r < 1 := by
    rw [← hi₀r]
    exact lt_of_le_of_ne (hz i₀) hi₀1
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  -- weights above the top radius vanish
  have habove : ∀ i, ‖z i‖ ≠ 1 → r < ‖z i‖ → c i = 0 := by
    intro i h1 hlt
    by_contra hne
    have hz0 : z i ≠ 0 := by
      intro h
      rw [h, norm_zero] at hlt
      linarith
    have := hmax ‖z i‖ ⟨i, rfl, h1, hz0, hne⟩
    linarith
  -- the tower normalized at the top radius
  set y : ι → ℂ := fun i => if ‖z i‖ ≤ r then z i / r else 1 with hy
  set c'' : ι → ℂ := fun i => if ‖z i‖ ≤ r then c i else 0 with hc''
  have hy1 : ∀ i, ‖y i‖ ≤ 1 := by
    intro i
    rw [hy]
    simp only
    split_ifs with h
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      exact (div_le_one hr0).mpr h
    · simp
  have hc''s : Summable fun i => ‖c'' i‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hc
    rw [hc'']
    simp only
    split_ifs <;> simp
  have hrel : ∀ ν, towerSum (innerWeight c z) z ν = (r : ℂ) ^ ν * towerSum c'' y ν := by
    intro ν
    rw [towerSum, towerSum, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [hy, hc'']
    simp only [innerWeight]
    by_cases h1 : ‖z i‖ = 1
    · have hnot : ¬ ‖z i‖ ≤ r := by rw [h1]; linarith
      rw [if_pos h1, if_neg hnot, if_neg hnot]
      simp
    · by_cases h2 : ‖z i‖ ≤ r
      · rw [if_neg h1, if_pos h2, if_pos h2, div_pow]
        field_simp
      · rw [if_neg h1, if_neg h2, if_neg h2, habove i h1 (lt_of_not_ge h2)]
        simp
  have h0 : Tendsto (towerSum c'' y) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hI] with ν hν
    have := hrel ν
    rw [hν] at this
    exact ((mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero ν hrC)).symm
  set w : ℂ := z i₀ / r with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hi₀r, div_self hr0.ne']
  have hm := merged_eq_zero_of_tendsto_zero hc''s hy1 h0 hw1
  have hsingle : (∑' i, if y i = w then c'' i else 0) = c i₀ := by
    have : ∀ i, (if y i = w then c'' i else 0) = if i = i₀ then c i else 0 := by
      intro i
      rw [hy, hc'', hw]
      simp only
      by_cases h2 : ‖z i‖ ≤ r
      · simp only [h2, if_true]
        by_cases h3 : i = i₀
        · simp [h3]
        · have hne : z i / (r : ℂ) ≠ z i₀ / r := by
            intro h
            apply h3
            apply hinj
            field_simp at h
            exact h
          simp [h3, hne]
      · have h3 : i ≠ i₀ := by
          intro h
          rw [h, hi₀r] at h2
          exact h2 le_rfl
        simp [h2, h3]
    rw [tsum_congr this, tsum_ite_eq]
  rw [hsingle] at hm
  exact hi₀c hm

/-- **Kronecker's theorem at infinite rank, distinct modes.** A summable tower of distinct modes in
the closed unit disc, whose moduli have no infinite ascending chain, with integer level sums at all
large levels, has finite rank: for one `τ ≥ 1` every visible mode other than `0` is a `τ`-th root of
unity, and only finitely many modes are visible. -/
theorem kronecker_oneFrobenius_injective {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hz : ∀ i, ‖z i‖ ≤ 1) (hinj : Function.Injective z)
    (hacc : ∀ S : Set ℝ, S ⊆ Set.range (fun i => ‖z i‖) → S.Nonempty → ∃ r ∈ S, ∀ t ∈ S, t ≤ r)
    (hint : ∀ᶠ ν : ℕ in atTop, ∃ n : ℤ, towerSum c z ν = n) :
    ∃ τ : ℕ, 1 ≤ τ ∧ (∀ i, c i ≠ 0 → z i ≠ 0 → z i ^ τ = 1) ∧
      {i | c i ≠ 0 ∧ z i ≠ 0}.Finite := by
  classical
  obtain ⟨τ, hτ1, hcircle, hinner⟩ := kronecker_oneFrobenius hc hz hint
  have hin := inner_weight_eq_zero hc hz hinj hacc hinner
  have hroot : ∀ i, c i ≠ 0 → z i ≠ 0 → z i ^ τ = 1 := by
    intro i hci hzi
    have h1 : ‖z i‖ = 1 := by
      by_contra h1
      exact hci (hin i h1 hzi)
    refine hcircle (z i) h1 ?_
    have : ∀ j, (if z j = z i then c j else 0) = if j = i then c j else 0 := by
      intro j
      by_cases h : j = i
      · simp [h]
      · have : z j ≠ z i := fun h' => h (hinj h')
        simp [h, this]
    rw [tsum_congr this, tsum_ite_eq]
    exact hci
  refine ⟨τ, hτ1, hroot, ?_⟩
  -- the visible modes inject into the `τ`-th roots of unity
  have hτpos : 0 < τ := hτ1
  have hfin : {x : ℂ | x ^ τ = 1}.Finite := by
    have hne : (Polynomial.X ^ τ - 1 : Polynomial ℂ) ≠ 0 :=
      Polynomial.X_pow_sub_C_ne_zero hτpos 1
    refine ((Polynomial.X ^ τ - 1 : Polynomial ℂ).roots.toFinset.finite_toSet).subset ?_
    intro x hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hne]
    simp only [Set.mem_setOf_eq] at hx
    simp [hx]
  refine (hfin.preimage (hinj.injOn)).subset ?_
  rintro i ⟨hci, hzi⟩
  exact hroot i hci hzi

end GaloisForLFunctions.InfiniteRankPurityTheory
