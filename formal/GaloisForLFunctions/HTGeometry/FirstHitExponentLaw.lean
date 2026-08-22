import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Transference

/-!
# The first-hit exponent of a vector that is not very well approximable

Dirichlet approximation puts the first return of `q β` into the `r`-neighbourhood of the integer
lattice by time `⌈1/r⌉^m`, for every `β`.  If in addition the simultaneous Diophantine exponent of
`β` is exactly `1/m` — that is, `β` is not very well approximable — then the return cannot happen
essentially sooner, and the two halves pin the logarithmic exponent to `m`.

## Main results

* `latticeDist` — distance to the nearest integer, and its comparison with `latticeClose`.
* `notMem_intRange_of_not_vwa` — a vector that is not very well approximable has no rational
  multiple in the integer lattice.
* `tendsto_firstHit_atTop` — hence the first hit time diverges as the radius shrinks.
* `tendsto_log_firstHit_div_log` — **the first-hit exponent is exactly `m`.**
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ}

/-! ### Distance to the integer lattice -/

/-- The distance from a real number to the nearest integer. -/
def latticeDist (x : ℝ) : ℝ := |x - round x|

theorem latticeDist_nonneg (x : ℝ) : 0 ≤ latticeDist x := abs_nonneg _

theorem latticeDist_le (x : ℝ) (p : ℤ) : latticeDist x ≤ |x - p| := round_le x p

theorem latticeClose_iff_latticeDist_lt (x r : ℝ) : latticeClose x r ↔ latticeDist x < r := by
  constructor
  · rintro ⟨p, hp⟩
    exact lt_of_le_of_lt (latticeDist_le x p) hp
  · intro h
    exact ⟨round x, h⟩

theorem latticeDist_eq_zero_iff {x : ℝ} : latticeDist x = 0 ↔ ∃ p : ℤ, x = (p : ℝ) := by
  constructor
  · intro h
    exact ⟨round x, sub_eq_zero.mp (abs_eq_zero.mp h)⟩
  · rintro ⟨p, rfl⟩
    simp [latticeDist]

/-! ### The first hit time -/

theorem firstHit_set_nonempty (β : Fin m → ℝ) {r : ℝ} (hr : 0 < r) :
    {q : ℕ | 1 ≤ q ∧ ∀ i, latticeClose ((q : ℝ) * β i) r}.Nonempty := by
  classical
  set Q : ℕ := ⌈1 / r⌉₊ with hQdef
  have hQpos : 0 < Q := by
    rw [hQdef]
    exact Nat.ceil_pos.mpr (by positivity)
  obtain ⟨q, hq1, _, hclose⟩ := exists_simultaneous_dirichlet β hQpos
  have hle : (1 : ℝ) / Q ≤ r := by
    have hQR : (1 : ℝ) / r ≤ Q := Nat.le_ceil _
    have hQpos' : (0 : ℝ) < Q := by exact_mod_cast hQpos
    rw [div_le_iff₀ hQpos']
    rw [div_le_iff₀ hr] at hQR
    nlinarith [hQR, hr, hQpos']
  exact ⟨q, hq1, fun i => latticeClose_mono (hclose i) hle⟩

theorem firstHit_mem (β : Fin m → ℝ) {r : ℝ} (hr : 0 < r) :
    1 ≤ firstHit β r ∧ ∀ i, latticeClose ((firstHit β r : ℝ) * β i) r :=
  Nat.sInf_mem (firstHit_set_nonempty β hr)

theorem one_le_firstHit (β : Fin m → ℝ) {r : ℝ} (hr : 0 < r) : 1 ≤ firstHit β r :=
  (firstHit_mem β hr).1

/-! ### Not very well approximable forces an irrational multiple structure -/

/-- A vector that is not very well approximable has no positive integer multiple inside the integer
lattice: such a multiple would make every further multiple an exact approximation. -/
theorem notMem_intRange_of_not_vwa {β : Fin m → ℝ}
    (h : ¬ KleinbockMargulis.VWA β) {q : ℕ} (hq : 1 ≤ q) :
    ∃ i, latticeDist ((q : ℝ) * β i) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  choose p hp using fun i => latticeDist_eq_zero_iff.mp (hcon i)
  refine h ⟨1, one_pos, ?_⟩
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (k + 1) * q) ?_ ?_
  · intro a b hab
    have hqpos : 0 < q := hq
    have : a + 1 = b + 1 := Nat.eq_of_mul_eq_mul_right hqpos hab
    omega
  · intro k
    refine ⟨?_, fun i => ((k + 1 : ℤ) * p i), fun i => ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · have hval : (((k + 1) * q : ℕ) : ℝ) * β i = ((((k + 1 : ℤ) * p i : ℤ)) : ℝ) := by
        push_cast
        rw [mul_assoc, hp i]
      rw [hval, sub_self, abs_zero]
      positivity

/-- The first hit time diverges as the radius shrinks. -/
theorem tendsto_firstHit_atTop {β : Fin m → ℝ} (h : ¬ KleinbockMargulis.VWA β) :
    Tendsto (fun r : ℝ => firstHit β r) (𝓝[>] (0 : ℝ)) atTop := by
  classical
  refine tendsto_atTop.mpr fun Q => ?_
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact Nat.zero_le _
  choose idx hidx using fun q : ℕ => fun hq : 1 ≤ q => notMem_intRange_of_not_vwa h hq
  have hne : (Finset.Icc 1 Q).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hQ⟩⟩
  set g : ℕ → ℝ := fun q =>
    if hq : 1 ≤ q then latticeDist ((q : ℝ) * β (idx q hq)) else 1 with hg
  set ρ : ℝ := (Finset.Icc 1 Q).inf' hne g with hρ
  have hρpos : 0 < ρ := by
    rw [hρ, Finset.lt_inf'_iff]
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    rw [hg]
    simp only [dif_pos hq1]
    exact lt_of_le_of_ne (latticeDist_nonneg _) (Ne.symm (hidx q hq1))
  filter_upwards [Ioo_mem_nhdsGT hρpos] with r hr
  obtain ⟨hr0, hrρ⟩ := hr
  by_contra hcon
  push Not at hcon
  have hq1 : 1 ≤ firstHit β r := one_le_firstHit β hr0
  have hmemIcc : firstHit β r ∈ Finset.Icc 1 Q :=
    Finset.mem_Icc.mpr ⟨hq1, le_of_lt hcon⟩
  have hclose := (firstHit_mem β hr0).2 (idx (firstHit β r) hq1)
  rw [latticeClose_iff_latticeDist_lt] at hclose
  have hle : ρ ≤ latticeDist ((firstHit β r : ℝ) * β (idx (firstHit β r) hq1)) := by
    have := Finset.inf'_le g hmemIcc
    rw [hg] at this
    simpa only [dif_pos hq1] using this
  linarith

/-! ### The exponent -/

theorem tendsto_log_one_div :
    Tendsto (fun r : ℝ => Real.log (1 / r)) (𝓝[>] (0 : ℝ)) atTop := by
  have h : Tendsto (fun r : ℝ => -Real.log r) (𝓝[>] (0 : ℝ)) atTop :=
    Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  simpa [one_div, Real.log_inv] using h

/-- The first hit time misses the Diophantine radius, so it is at least `r^{-1/c}`. -/
theorem rpow_lt_cast_of_hit_of_not_approx {β : Fin m → ℝ} {c r : ℝ} {q : ℕ}
    (hc : 0 < c) (hq : 0 < q)
    (hnot : ¬ ∃ p : Fin m → ℤ, ∀ i, |(q : ℝ) * β i - (p i : ℝ)| ≤ (q : ℝ) ^ (-c))
    (hhit : ∀ i, latticeClose ((q : ℝ) * β i) r) :
    r ^ (-(1 / c)) < (q : ℝ) := by
  refine rpow_lt_cast_of_hit hc hq ?_ hhit
  by_contra hfail
  push Not at hfail
  refine hnot ⟨fun i => round ((q : ℝ) * β i), fun i => ?_⟩
  obtain ⟨pi, hpi⟩ := hfail i
  exact le_of_lt (lt_of_le_of_lt (latticeDist_le _ pi) hpi)

/-- **The Dirichlet half of the exponent.**  For every spectrum the first hit time is at most the
pigeonhole cost, so its logarithmic exponent is at most `m` up to a vanishing correction. -/
theorem log_firstHit_div_log_le (β : Fin m → ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.log (firstHit β r) / Real.log (1 / r)
      ≤ (m : ℝ) + m * (Real.log (1 + r) / Real.log (1 / r)) := by
  have hinv : 1 < 1 / r := by
    rw [lt_div_iff₀ hr0]
    linarith
  have hlogpos : 0 < Real.log (1 / r) := Real.log_pos hinv
  have hceil : ((⌈1 / r⌉₊ : ℝ)) ≤ 1 / r + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hle : (firstHit β r : ℝ) ≤ (1 / r + 1) ^ m := by
    have h1 := firstHit_le β hr0
    calc (firstHit β r : ℝ) ≤ ((⌈1 / r⌉₊ ^ m : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ((⌈1 / r⌉₊ : ℝ)) ^ m := by push_cast; ring
      _ ≤ (1 / r + 1) ^ m := pow_le_pow_left₀ (by positivity) hceil m
  have hfpos : (0 : ℝ) < firstHit β r := by
    have := one_le_firstHit β hr0
    exact_mod_cast this
  have hlog : Real.log (firstHit β r) ≤ (m : ℝ) * Real.log (1 / r + 1) := by
    have h := Real.log_le_log hfpos hle
    rwa [Real.log_pow] at h
  have hsplit : Real.log (1 / r + 1) = Real.log (1 + r) + Real.log (1 / r) := by
    have hfac : 1 / r + 1 = (1 + r) * (1 / r) := by field_simp
    rw [hfac, Real.log_mul (by positivity) (by positivity)]
  rw [div_le_iff₀ hlogpos]
  have hrhs : ((m : ℝ) + m * (Real.log (1 + r) / Real.log (1 / r))) * Real.log (1 / r)
      = (m : ℝ) * (Real.log (1 + r) + Real.log (1 / r)) := by
    field_simp
    ring
  rw [hrhs, ← hsplit]
  exact hlog

theorem tendsto_dirichletCorrection (m : ℕ) :
    Tendsto (fun r : ℝ => (m : ℝ) + m * (Real.log (1 + r) / Real.log (1 / r)))
      (𝓝[>] (0 : ℝ)) (𝓝 (m : ℝ)) := by
  have hcont : ContinuousAt (fun r : ℝ => Real.log (1 + r)) 0 :=
    (continuousAt_const.add continuousAt_id).log (by norm_num)
  have hnum : Tendsto (fun r : ℝ => Real.log (1 + r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h
  have hratio :
      Tendsto (fun r : ℝ => Real.log (1 + r) / Real.log (1 / r)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hnum.div_atTop tendsto_log_one_div
  have h := (tendsto_const_nhds (x := (m : ℝ)) (f := 𝓝[>] (0 : ℝ))).add
    ((tendsto_const_nhds (x := (m : ℝ)) (f := 𝓝[>] (0 : ℝ))).mul hratio)
  simpa using h

/-- **The first-hit exponent law.**  If the simultaneous Diophantine exponent of `β` is exactly
`1/m`, the first return of `q β` to the `r`-neighbourhood of the integer lattice has logarithmic
exponent exactly `m`. -/
theorem tendsto_log_firstHit_div_log (hm : 0 < m) {β : Fin m → ℝ}
    (h : ¬ KleinbockMargulis.VWA β) :
    Tendsto (fun r : ℝ => Real.log (firstHit β r) / Real.log (1 / r)) (𝓝[>] (0 : ℝ))
      (𝓝 (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    rcases le_or_gt b 0 with hb0 | hb0
    · have hfh : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 ≤ firstHit β r :=
        (tendsto_firstHit_atTop h).eventually_ge_atTop 2
      filter_upwards [hfh, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with r hfhr hr
      obtain ⟨hr0, hr1⟩ := hr
      have hinv : 1 < 1 / r := by
        rw [lt_div_iff₀ hr0]
        linarith
      have hlogpos : 0 < Real.log (1 / r) := Real.log_pos hinv
      have hnum : 0 < Real.log (firstHit β r) := by
        refine Real.log_pos ?_
        have : (2 : ℝ) ≤ (firstHit β r : ℝ) := by exact_mod_cast hfhr
        linarith
      have hpos : 0 < Real.log (firstHit β r) / Real.log (1 / r) := div_pos hnum hlogpos
      linarith
    · set ε : ℝ := (1 / b - 1 / (m : ℝ)) / 2 with hε
      have hlt : 1 / (m : ℝ) < 1 / b := one_div_lt_one_div_of_lt hb0 hb
      have hεpos : 0 < ε := by
        rw [hε]
        linarith
      set c : ℝ := 1 / (m : ℝ) + ε with hc
      have hcpos : 0 < c := by
        rw [hc]
        have hmi : (0 : ℝ) < 1 / (m : ℝ) := by positivity
        linarith
      have hcb : b < 1 / c := by
        have hcle : c < 1 / b := by
          rw [hc, hε]
          linarith
        rw [lt_div_iff₀ hcpos]
        rw [lt_div_iff₀ hb0] at hcle
        linarith [mul_comm b c]
      have hfin :
          {q : ℕ | 1 ≤ q ∧ ∃ p : Fin m → ℤ, ∀ i,
            |(q : ℝ) * β i - (p i : ℝ)| ≤ (q : ℝ) ^ (-((m : ℝ))⁻¹ - ε)}.Finite :=
        Set.not_infinite.mp fun hinf => h ⟨ε, hεpos, hinf⟩
      obtain ⟨Q, hQ⟩ := hfin.bddAbove
      have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), Q < firstHit β r :=
        (tendsto_firstHit_atTop h).eventually_gt_atTop Q
      filter_upwards [hev, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with r hQr hr
      obtain ⟨hr0, hr1⟩ := hr
      have hq1 : 1 ≤ firstHit β r := one_le_firstHit β hr0
      have hexp : -((m : ℝ))⁻¹ - ε = -c := by
        rw [hc, one_div]
        ring
      have hnot : ¬ ∃ p : Fin m → ℤ, ∀ i,
          |((firstHit β r : ℕ) : ℝ) * β i - (p i : ℝ)| ≤ ((firstHit β r : ℕ) : ℝ) ^ (-c) := by
        intro hex
        have hmem : firstHit β r ∈
            {q : ℕ | 1 ≤ q ∧ ∃ p : Fin m → ℤ, ∀ i,
              |(q : ℝ) * β i - (p i : ℝ)| ≤ (q : ℝ) ^ (-((m : ℝ))⁻¹ - ε)} := by
          refine ⟨hq1, ?_⟩
          rw [hexp]
          exact hex
        exact absurd (hQ hmem) (not_le.mpr hQr)
      have hhit := (firstHit_mem β hr0).2
      have hlow := rpow_lt_cast_of_hit_of_not_approx hcpos hq1 hnot hhit
      have hinv : 1 < 1 / r := by
        rw [lt_div_iff₀ hr0]
        linarith
      have hlogpos : 0 < Real.log (1 / r) := Real.log_pos hinv
      have hlogq : (1 / c) * Real.log (1 / r) < Real.log (firstHit β r) := by
        have h1 : Real.log (r ^ (-(1 / c))) < Real.log (firstHit β r) :=
          Real.log_lt_log (by positivity) hlow
        rwa [Real.log_rpow hr0, show -(1 / c) * Real.log r = (1 / c) * Real.log (1 / r) by
          rw [one_div r, Real.log_inv]; ring] at h1
      have hfinal : 1 / c < Real.log (firstHit β r) / Real.log (1 / r) :=
        (lt_div_iff₀ hlogpos).2 hlogq
      linarith
  · intro b hb
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        (m : ℝ) + m * (Real.log (1 + r) / Real.log (1 / r)) < b :=
      (tendsto_dirichletCorrection m).eventually_lt_const hb
    filter_upwards [hev, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with r hbr hr
    obtain ⟨hr0, hr1⟩ := hr
    exact lt_of_le_of_lt (log_firstHit_div_log_le β hr0 hr1) hbr

end

end GaloisForLFunctions.HTGeometry
