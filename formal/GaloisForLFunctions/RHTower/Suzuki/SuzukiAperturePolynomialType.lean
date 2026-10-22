import GaloisForLFunctions.RHTower.Suzuki.SuzukiApertureAlmostEvery

/-!
# `(26)`--`(28)`: almost every aperture has finite logarithmic type

The apertures approximated to *polynomial* depth `(2+N)^{-q}` by some valuation of `ℓ¹` length `N`
form a set of measure at most `(2N+1)^{#P}(2+N)^{-q}`.  That majorant is summable once `q` exceeds
the rank by more than one, so Borel--Cantelli leaves almost every aperture approximated only
finitely often — and an aperture that is not approximated has its opposite-end event clock bounded
by `q log(2+|ν|₁)`, which is finite logarithmic type.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- `(26)`: the set of apertures approximated at polynomial depth `(2+N)^{-q}` by a valuation of
length `N`. -/
def apertureApproxSetPoly {P : Type*} [Fintype P] [DecidableEq P] (ℓ : (P → ℤ) → ℝ) (q : ℝ)
    (N : ℕ) : Set ℝ :=
  ⋃ ν ∈ orbitLevel P N, {a : ℝ | |2 * a - ℓ ν| < (2 + (N : ℝ)) ^ (-q)}

theorem apertureApproxSetPoly_subset {P : Type*} [Fintype P] [DecidableEq P] (ℓ : (P → ℤ) → ℝ)
    (q : ℝ) (N : ℕ) :
    apertureApproxSetPoly ℓ q N
      ⊆ ⋃ ν ∈ orbitLevel P N,
          Ioo ((ℓ ν - (2 + (N : ℝ)) ^ (-q)) / 2) ((ℓ ν + (2 + (N : ℝ)) ^ (-q)) / 2) := by
  intro a ha
  rw [apertureApproxSetPoly, mem_iUnion₂] at ha
  obtain ⟨ν, hν, hlt⟩ := ha
  simp only [Set.mem_setOf_eq] at hlt
  rw [mem_iUnion₂]
  refine ⟨ν, hν, ?_⟩
  have habs := abs_lt.mp hlt
  constructor
  · linarith [habs.1]
  · linarith [habs.2]

theorem measurableSet_apertureApproxSetPoly {P : Type*} [Fintype P] [DecidableEq P]
    (ℓ : (P → ℤ) → ℝ) (q : ℝ) (N : ℕ) : MeasurableSet (apertureApproxSetPoly ℓ q N) := by
  rw [apertureApproxSetPoly]
  refine Finset.measurableSet_biUnion _ fun ν _ => ?_
  have hcont : Continuous fun a : ℝ => |2 * a - ℓ ν| := by fun_prop
  exact measurableSet_lt (hcont.measurable) measurable_const

/-- **`(27)`: the measure of the polynomially approximated apertures at length `N`.** -/
theorem volume_apertureApproxSetPoly_le {P : Type*} [Fintype P] [DecidableEq P]
    (ℓ : (P → ℤ) → ℝ) (q : ℝ) (N : ℕ) :
    volume (apertureApproxSetPoly ℓ q N)
      ≤ ENNReal.ofReal ((2 * N + 1) ^ Fintype.card P * (2 + (N : ℝ)) ^ (-q)) := by
  have hdpos : (0 : ℝ) < (2 + (N : ℝ)) ^ (-q) := Real.rpow_pos_of_pos (by positivity) _
  have hsub := apertureApproxSetPoly_subset ℓ q N
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have hterm : ∀ ν ∈ orbitLevel P N,
      volume (Ioo ((ℓ ν - (2 + (N : ℝ)) ^ (-q)) / 2) ((ℓ ν + (2 + (N : ℝ)) ^ (-q)) / 2))
        ≤ ENNReal.ofReal ((2 + (N : ℝ)) ^ (-q)) := by
    intro ν _
    rw [Real.volume_Ioo]
    apply ENNReal.ofReal_le_ofReal
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((orbitLevel P N).card : ℝ≥0∞) ≤ ((2 * N + 1) ^ Fintype.card P : ℕ) := by
    exact_mod_cast Nat.cast_le.mpr (card_orbitLevel_le N)
  refine le_trans (mul_le_mul' hcard (le_refl (ENNReal.ofReal ((2 + (N : ℝ)) ^ (-q))))) ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply le_of_eq
  congr 1
  push_cast
  ring

/-- The polynomial approximation majorant is summable past rank plus one. -/
theorem summable_polyApertureMajorant (d : ℕ) {q : ℝ} (hq : (d : ℝ) + 1 < q) :
    Summable fun N : ℕ => (2 * (N : ℝ) + 1) ^ d * (2 + (N : ℝ)) ^ (-q) := by
  have hbase : Summable fun N : ℕ => ((2 : ℝ) + (N : ℝ)) ^ ((d : ℝ) - q) := by
    have h1 : Summable fun N : ℕ => ((N : ℝ)) ^ ((d : ℝ) - q) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have h2 : Summable fun N : ℕ => (((N + 2 : ℕ) : ℝ)) ^ ((d : ℝ) - q) :=
      (summable_nat_add_iff 2).mpr h1
    refine h2.congr fun N => ?_
    congr 1
    push_cast
    ring
  have hdom : Summable fun N : ℕ => (3 : ℝ) ^ d * ((2 + (N : ℝ)) ^ ((d : ℝ) - q)) :=
    hbase.mul_left _
  refine hdom.of_nonneg_of_le (fun N => by positivity) ?_
  intro N
  have hpos : (0 : ℝ) < 2 + (N : ℝ) := by positivity
  have hsplit : (2 + (N : ℝ)) ^ ((d : ℝ) - q)
      = (2 + (N : ℝ)) ^ (d : ℕ) * (2 + (N : ℝ)) ^ (-q) := by
    rw [← Real.rpow_natCast (2 + (N : ℝ)) d, ← Real.rpow_add hpos, sub_eq_add_neg]
  rw [hsplit]
  have hbound : (2 * (N : ℝ) + 1) ^ d ≤ 3 ^ d * (2 + (N : ℝ)) ^ d := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hdpos : (0 : ℝ) < (2 + (N : ℝ)) ^ (-q) := Real.rpow_pos_of_pos hpos _
  nlinarith [hbound, hdpos]

/-- **`(28)`, Borel--Cantelli: almost every aperture is polynomially approximated only finitely
often.** -/
theorem ae_finite_apertureApproxPoly {P : Type*} [Fintype P] [DecidableEq P]
    (ℓ : (P → ℤ) → ℝ) {q : ℝ} (hq : (Fintype.card P : ℝ) + 1 < q) :
    ∀ᵐ a : ℝ, a ∉ Filter.atTop.limsup (apertureApproxSetPoly ℓ q) := by
  have hmaj := summable_polyApertureMajorant (Fintype.card P) hq
  have hnn : ∀ N : ℕ, 0 ≤ (2 * (N : ℝ) + 1) ^ Fintype.card P * (2 + (N : ℝ)) ^ (-q) := by
    intro N
    have : (0 : ℝ) < (2 + (N : ℝ)) ^ (-q) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  have hsum : (∑' N : ℕ, volume (apertureApproxSetPoly ℓ q N)) ≠ ⊤ := by
    have hle : ∀ N : ℕ, volume (apertureApproxSetPoly ℓ q N)
        ≤ ENNReal.ofReal ((2 * (N : ℝ) + 1) ^ Fintype.card P * (2 + (N : ℝ)) ^ (-q)) := by
      intro N
      have h := volume_apertureApproxSetPoly_le ℓ q N
      refine le_trans h (le_of_eq ?_)
      congr 1
    have hbound : (∑' N : ℕ, volume (apertureApproxSetPoly ℓ q N))
        ≤ ∑' N : ℕ,
            ENNReal.ofReal ((2 * (N : ℝ) + 1) ^ Fintype.card P * (2 + (N : ℝ)) ^ (-q)) :=
      ENNReal.tsum_le_tsum hle
    have hfin : (∑' N : ℕ,
        ENNReal.ofReal ((2 * (N : ℝ) + 1) ^ Fintype.card P * (2 + (N : ℝ)) ^ (-q))) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hnn hmaj]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hfin hbound
  have hzero := measure_limsup_atTop_eq_zero hsum
  rw [ae_iff]
  simpa using hzero

/-- `(2)`: the opposite-end event clock of an aperture. -/
def apertureEventClock {P : Type*} [Fintype P] (ℓ : (P → ℤ) → ℝ) (a : ℝ) (ν : P → ℤ) : ℝ :=
  max 0 (-Real.log |2 * a - ℓ ν|)

/-- Valuations of bounded `ℓ¹` length form a finite set. -/
theorem finite_orbitLength_lt {P : Type*} [Fintype P] [DecidableEq P] (N₀ : ℕ) :
    {ν : P → ℤ | orbitLength ν < N₀}.Finite := by
  refine Set.Finite.subset
    (Finset.finite_toSet (Fintype.piFinset fun _ : P => Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ))) ?_
  intro ν hν
  have hlt : orbitLength ν < N₀ := hν
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro p
  rw [Finset.mem_Icc]
  have hp : (ν p).natAbs ≤ orbitLength ν := by
    rw [orbitLength]
    exact Finset.single_le_sum (f := fun r => (ν r).natAbs) (fun r _ => Nat.zero_le _)
      (Finset.mem_univ p)
  omega

/-- **`(28)`: an aperture that is polynomially approximated only finitely often has finite
logarithmic type.** -/
theorem eventually_apertureEventClock_le {P : Type*} [Fintype P] [DecidableEq P]
    {ℓ : (P → ℤ) → ℝ} {q a : ℝ} (hq : 0 ≤ q)
    (ha : a ∉ Filter.atTop.limsup (apertureApproxSetPoly ℓ q)) :
    ∀ᶠ ν in Filter.cofinite,
      apertureEventClock ℓ a ν ≤ q * Real.log (2 + (orbitLength ν : ℝ)) := by
  have hfreq : ¬ ∃ᶠ N in Filter.atTop, a ∈ apertureApproxSetPoly ℓ q N := by
    intro hcon
    exact ha (Filter.mem_limsup_iff_frequently_mem.mpr hcon)
  rw [Filter.not_frequently] at hfreq
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hfreq
  have hcof : {ν : P → ℤ | orbitLength ν < N₀}.Finite := finite_orbitLength_lt N₀
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset hcof ?_
  intro ν hν
  by_contra hcon
  simp only [Set.mem_setOf_eq, not_lt] at hcon
  refine hν ?_
  set L : ℕ := orbitLength ν with hLdef
  have hbad := hN₀ L hcon
  have hnot : a ∉ {b : ℝ | |2 * b - ℓ ν| < (2 + (L : ℝ)) ^ (-q)} := by
    intro hmem
    refine hbad ?_
    rw [apertureApproxSetPoly, Set.mem_iUnion₂]
    exact ⟨ν, mem_orbitLevel rfl, hmem⟩
  simp only [Set.mem_setOf_eq, not_lt] at hnot
  have hpos2 : (0 : ℝ) < 2 + (L : ℝ) := by positivity
  have hdpos : (0 : ℝ) < (2 + (L : ℝ)) ^ (-q) := Real.rpow_pos_of_pos hpos2 _
  have habs : (0 : ℝ) < |2 * a - ℓ ν| := lt_of_lt_of_le hdpos hnot
  have hlog : Real.log ((2 + (L : ℝ)) ^ (-q)) ≤ Real.log |2 * a - ℓ ν| :=
    Real.log_le_log hdpos hnot
  have hlogval : Real.log ((2 + (L : ℝ)) ^ (-q)) = -q * Real.log (2 + (L : ℝ)) := by
    rw [Real.log_rpow hpos2]
  rw [hlogval] at hlog
  have hlogpos : 0 ≤ Real.log (2 + (L : ℝ)) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ (L : ℝ) := by positivity
    linarith
  rw [apertureEventClock, max_le_iff]
  constructor
  · positivity
  · linarith [hlog]

end

end RHTower
