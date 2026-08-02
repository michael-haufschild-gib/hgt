import GaloisForLFunctions.HTGeometry.TorusCoveringNumbers

/-!
# The box dimension of a phase torus

The grid cover and the Haar lower bound trap the covering number of the `k`-dimensional phase torus
between constant multiples of `ε^{-k}`, so its box dimension is exactly `k`.

This is the model case of the completed-orbit dimension theorem: the orbit closure of a finite
frequency packet is a continuous injective image of such a torus.
-/

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

theorem coveringCard_le_of_externalCoveringNumber_le {A : Set X} {ε : ℝ≥0} {n : ℕ}
    (h : Metric.externalCoveringNumber ε A ≤ (n : ℕ∞)) : coveringCard ε A ≤ (n : ℝ) := by
  have hmono : (Metric.externalCoveringNumber ε A).toENNReal ≤ (n : ℝ≥0∞) := by
    simpa using (ENat.toENNReal_le).2 h
  have hfin : (Metric.externalCoveringNumber ε A).toENNReal ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hmono
  have := ENNReal.toReal_mono (by simp) hmono
  simpa [coveringCard] using this

theorem le_coveringCard_of_le {A : Set X} {ε : ℝ≥0} {r : ℝ≥0∞} {n : ℕ}
    (hfin : Metric.externalCoveringNumber ε A ≤ (n : ℕ∞))
    (h : r ≤ (Metric.externalCoveringNumber ε A).toENNReal) :
    r.toReal ≤ coveringCard ε A := by
  have hmono : (Metric.externalCoveringNumber ε A).toENNReal ≤ (n : ℝ≥0∞) := by
    simpa using (ENat.toENNReal_le).2 hfin
  have hne : (Metric.externalCoveringNumber ε A).toENNReal ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hmono
  exact ENNReal.toReal_mono hne h

/-- A finite external covering number is attained by some cover. -/
theorem exists_isCover_encard_eq {A : Set X} {ε : ℝ≥0}
    (h : Metric.externalCoveringNumber ε A ≠ ⊤) :
    ∃ C : Set X, Metric.IsCover ε A C ∧ C.encard = Metric.externalCoveringNumber ε A := by
  have hlt : Metric.externalCoveringNumber ε A < Metric.externalCoveringNumber ε A + 1 :=
    ENat.lt_add_one_iff h |>.mpr le_rfl
  rw [Metric.externalCoveringNumber] at hlt
  obtain ⟨C, hC⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hCcov, hCle⟩ := iInf_lt_iff.mp hC
  refine ⟨C, hCcov, le_antisymm ?_ ?_⟩
  · exact (ENat.lt_add_one_iff h).mp hCle
  · exact iInf₂_le_of_le C hCcov le_rfl

/-- A lower bound valid for every cover is a lower bound for the covering number. -/
theorem le_coveringCard_of_forall_isCover {A : Set X} {ε : ℝ≥0} {L : ℝ} {n : ℕ}
    (hfin : Metric.externalCoveringNumber ε A ≤ (n : ℕ∞))
    (hL : ∀ C : Set X, Metric.IsCover ε A C → C.Finite →
      L ≤ ((C.encard : ℕ∞) : ℝ≥0∞).toReal) :
    L ≤ coveringCard ε A := by
  have hne : Metric.externalCoveringNumber ε A ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hfin
  obtain ⟨C, hC, hCeq⟩ := exists_isCover_encard_eq hne
  have hCfin : C.Finite := by
    rw [← Set.encard_ne_top_iff, hCeq]
    exact hne
  have hval := hL C hC hCfin
  rw [hCeq] at hval
  exact hval

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- The upper covering estimate of the phase torus at an arbitrary small resolution. -/
theorem coveringCard_torus_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    coveringCard ε.toNNReal (Set.univ : Set (UnitAddTorus k))
      ≤ (2 : ℝ) ^ Fintype.card k * (1 / ε) ^ Fintype.card k := by
  set n : ℕ := ⌈1 / ε⌉₊ with hn
  have hinvpos : (0 : ℝ) < 1 / ε := by positivity
  have hnpos : 0 < n := Nat.ceil_pos.mpr hinvpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hge : (1 : ℝ) / ε ≤ n := Nat.le_ceil _
  have hradius : (1 : ℝ) / (2 * n) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ ε * n := by
      rw [div_le_iff₀ hε] at hge
      nlinarith [hge]
    nlinarith [hε.le, hnR]
  have hle : Real.toNNReal (1 / (2 * n)) ≤ ε.toNNReal := Real.toNNReal_mono hradius
  have hcov : Metric.externalCoveringNumber ε.toNNReal (Set.univ : Set (UnitAddTorus k))
      ≤ ((n ^ Fintype.card k : ℕ) : ℕ∞) :=
    le_trans (Metric.externalCoveringNumber_anti hle) (externalCoveringNumber_torus_le n hnpos)
  have hreal := coveringCard_le_of_externalCoveringNumber_le hcov
  refine le_trans hreal ?_
  have hnle : (n : ℝ) ≤ 2 * (1 / ε) := by
    have hceil : (n : ℝ) < 1 / ε + 1 := by
      rw [hn]
      exact Nat.ceil_lt_add_one hinvpos.le
    have hone : (1 : ℝ) ≤ 1 / ε := by
      rw [le_div_iff₀ hε]
      linarith
    linarith
  calc ((n ^ Fintype.card k : ℕ) : ℝ) = (n : ℝ) ^ Fintype.card k := by push_cast; ring
    _ ≤ (2 * (1 / ε)) ^ Fintype.card k := by
        exact pow_le_pow_left₀ (le_of_lt hnR) hnle _
    _ = (2 : ℝ) ^ Fintype.card k * (1 / ε) ^ Fintype.card k := by rw [mul_pow]

/-- The lower covering estimate of the phase torus. -/
theorem le_coveringCard_torus {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    (1 / 4 : ℝ) ^ Fintype.card k * (1 / ε) ^ Fintype.card k
      ≤ coveringCard ε.toNNReal (Set.univ : Set (UnitAddTorus k)) := by
  have hε1 : ε ≤ 1 := by linarith
  set n : ℕ := ⌈1 / ε⌉₊ with hn
  have hinvpos : (0 : ℝ) < 1 / ε := by positivity
  have hnpos : 0 < n := Nat.ceil_pos.mpr hinvpos
  have hge : (1 : ℝ) / ε ≤ n := Nat.le_ceil _
  have hradius : (1 : ℝ) / (2 * n) ≤ ε := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ ε * n := by
      rw [div_le_iff₀ hε] at hge
      nlinarith [hge]
    nlinarith [hε.le, hnR]
  have hle : Real.toNNReal (1 / (2 * n)) ≤ ε.toNNReal := Real.toNNReal_mono hradius
  have hfin : Metric.externalCoveringNumber ε.toNNReal (Set.univ : Set (UnitAddTorus k))
      ≤ ((n ^ Fintype.card k : ℕ) : ℕ∞) :=
    le_trans (Metric.externalCoveringNumber_anti hle) (externalCoveringNumber_torus_le n hnpos)
  have hεNN : ((ε.toNNReal : ℝ≥0) : ℝ) = ε := Real.coe_toNNReal ε hε.le
  have hpos : (0 : ℝ) < 2 * (2 * ε) := by linarith
  refine le_coveringCard_of_forall_isCover hfin ?_
  intro C hC hCfin
  have hbound := one_le_encard_mul_of_isCover_torus (k := k) (ε := ε.toNNReal)
    (by rw [hεNN]; exact hε) (by rw [hεNN]; exact hε4) hC
  rw [hεNN] at hbound
  set x : ℝ≥0∞ := ((C.encard : ℕ∞) : ℝ≥0∞) with hx
  have hxfin : x ≠ ⊤ := by
    rw [hx]
    simpa using (Set.encard_ne_top_iff).2 hCfin
  have hmfin : (ENNReal.ofReal (2 * (2 * ε)) ^ Fintype.card k) ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hreal : (1 : ℝ) ≤ x.toReal * ((2 * (2 * ε)) ^ Fintype.card k) := by
    have hmul := ENNReal.toReal_mono (by
      exact ENNReal.mul_ne_top hxfin hmfin) hbound
    rw [ENNReal.toReal_mul, ENNReal.toReal_one] at hmul
    rw [← ENNReal.ofReal_pow hpos.le, ENNReal.toReal_ofReal (by positivity)] at hmul
    exact hmul
  have hmpos : (0 : ℝ) < (2 * (2 * ε)) ^ Fintype.card k := by positivity
  have hxlow : ((2 * (2 * ε)) ^ Fintype.card k)⁻¹ ≤ x.toReal := by
    rw [inv_le_iff_one_le_mul₀ hmpos]
    linarith [hreal]
  refine le_trans (le_of_eq ?_) hxlow
  rw [← mul_pow, ← inv_pow]
  congr 1
  field_simp
  norm_num

/-- **The box dimension of a phase torus is its dimension.** -/
theorem hasBoxDim_torus :
    HasBoxDim (Set.univ : Set (UnitAddTorus k)) (Fintype.card k) := by
  refine hasBoxDim_of_covering_bounds (c₁ := (1 / 4 : ℝ) ^ Fintype.card k)
    (c₂ := (2 : ℝ) ^ Fintype.card k) (ε₀ := 1 / 4) (by positivity) (by positivity) (by norm_num)
    (fun ε hε hε₀ => le_coveringCard_torus hε (le_of_lt hε₀))
    (fun ε hε hε₀ => coveringCard_torus_le hε (by linarith))

end

end GaloisForLFunctions.HTGeometry
