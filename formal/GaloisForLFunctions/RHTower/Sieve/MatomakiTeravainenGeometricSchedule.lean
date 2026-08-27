import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAdjacentSchedule

/-!
# Geometric source schedule for Matomäki--Teräväinen Lemma 2.3(ii)

The source uses real levels `Q_j = (1 + δ_A)^j`.  Natural sifting cutoffs are ceilings, while
the prime block `(Q_j,Q_{j+1}]` has integer endpoints `⌊Q_j⌋₊ + 1` and
`⌊Q_{j+1}⌋₊ + 1`.  Keeping these two roundings separate is necessary when a level is integral.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Right-open natural endpoint representing the real condition `q ≤ Q`. -/
def mtRealBlockEndpoint (Q : ℕ → ℝ) (j : ℕ) : ℕ :=
  Nat.floor (Q j) + 1

/-- Natural sifting cutoff representing the real condition `p < W`. -/
def mtRealSiftCutoff {t : ℕ} (W : Fin (t + 1) → ℝ) (j : Fin (t + 1)) : ℕ :=
  Nat.ceil (W j)

/-- Exact real meaning of a rounded sifting cutoff. -/
theorem lt_mtRealSiftCutoff_iff {t : ℕ} (W : Fin (t + 1) → ℝ)
    (j : Fin (t + 1)) (p : ℕ) :
    p < mtRealSiftCutoff W j ↔ (p : ℝ) < W j := by
  exact Nat.lt_ceil

/-- Exact real meaning of a rounded adjacent prime block. -/
theorem mem_mtAdjacentPrimeBlock_real_iff {t : ℕ} (Q : ℕ → ℝ)
    (hQnonneg : ∀ j, 0 ≤ Q j) (i : Fin t) (q : ℕ) :
    q ∈ mtAdjacentPrimeBlock (mtRealBlockEndpoint Q) i ↔
      Q i.1 < (q : ℝ) ∧ (q : ℝ) ≤ Q (i.1 + 1) ∧ q.Prime := by
  rw [mtAdjacentPrimeBlock, mem_primesIco]
  constructor
  · rintro ⟨hqLower, hqUpper, hqPrime⟩
    have hfloorLower : Nat.floor (Q i.1) < q := by
      simpa [mtRealBlockEndpoint] using hqLower
    have hqLowerReal : Q i.1 < (q : ℝ) :=
      (Nat.floor_lt (hQnonneg i.1)).mp hfloorLower
    have hqFloorUpper : q ≤ Nat.floor (Q (i.1 + 1)) := by
      simp [mtRealBlockEndpoint] at hqUpper
      omega
    have hfloorReal :
        ((Nat.floor (Q (i.1 + 1)) : ℕ) : ℝ) ≤ Q (i.1 + 1) :=
      Nat.floor_le (hQnonneg (i.1 + 1))
    have hqFloorUpperReal :
        (q : ℝ) ≤ ((Nat.floor (Q (i.1 + 1)) : ℕ) : ℝ) := by
      exact_mod_cast hqFloorUpper
    exact ⟨hqLowerReal, hqFloorUpperReal.trans hfloorReal, hqPrime⟩
  · rintro ⟨hqLower, hqUpper, hqPrime⟩
    have hfloorLower : Nat.floor (Q i.1) < q :=
      (Nat.floor_lt (hQnonneg i.1)).mpr hqLower
    have hqFloorUpper : q ≤ Nat.floor (Q (i.1 + 1)) :=
      Nat.le_floor hqUpper
    constructor
    · simp [mtRealBlockEndpoint]
      omega
    · constructor
      · simp [mtRealBlockEndpoint]
        omega
      · exact hqPrime

/-- A real adjacent schedule satisfying the source endpoint inequalities gives finite source
data.  `W` permits the root cutoff `z₁` to differ from the right endpoint of the final block. -/
def MTFiniteIterationSourceData.ofRealAdjacentSchedule {t : ℕ}
    (z₀ D : ℕ) (Q : ℕ → ℝ) (W : Fin (t + 1) → ℝ)
    (hQnonneg : ∀ j, 0 ≤ Q j)
    (hQmono : Monotone Q)
    (hz₀Q : (z₀ : ℝ) ≤ Q 0)
    (hz₀W : ∀ j, (z₀ : ℝ) ≤ W j)
    (hWQ : ∀ j, W j ≤ Q j.1)
    (hQ₀W : ∀ i : Fin t, Q 0 < W i.succ) :
    MTFiniteIterationSourceData t := by
  apply MTFiniteIterationSourceData.ofAdjacentSchedule z₀ D
    (mtRealBlockEndpoint Q) (mtRealSiftCutoff W)
  · intro a b hab
    exact Nat.add_le_add_right (Nat.floor_mono (hQmono hab)) 1
  · exact (Nat.le_floor hz₀Q).trans (Nat.le_add_right _ _)
  · intro j
    have hceil : Nat.ceil ((z₀ : ℕ) : ℝ) ≤ Nat.ceil (W j) :=
      Nat.ceil_mono (hz₀W j)
    simpa [mtRealSiftCutoff, Nat.ceil_natCast] using hceil
  · intro j
    apply (Nat.ceil_le).mpr
    have hQfloor : Q j.1 < ((Nat.floor (Q j.1) + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (Q j.1)
    exact (hWQ j).trans hQfloor.le
  · intro i
    have hfloorCeil : Nat.floor (Q 0) < Nat.ceil (W i.succ) :=
      (Nat.floor_lt (hQnonneg 0)).mpr
        ((hQ₀W i).trans_le (Nat.le_ceil (W i.succ)))
    simp only [mtRealBlockEndpoint, mtRealSiftCutoff]
    omega

/-- Rooted real schedule: internal cutoffs are `Q_j`, while the last cutoff is literal `z₁`. -/
def mtRootedRealCutoff {t : ℕ} (Q : ℕ → ℝ) (z₁ : ℝ) : Fin (t + 1) → ℝ :=
  Fin.lastCases z₁ (fun i => Q i.1)

@[simp] theorem mtRootedRealCutoff_last {t : ℕ} (Q : ℕ → ℝ) (z₁ : ℝ) :
    mtRootedRealCutoff Q z₁ (Fin.last t) = z₁ := by
  simp [mtRootedRealCutoff]

@[simp] theorem mtRootedRealCutoff_castSucc {t : ℕ} (Q : ℕ → ℝ) (z₁ : ℝ)
    (i : Fin t) :
    mtRootedRealCutoff Q z₁ i.castSucc = Q i.1 := by
  simp [mtRootedRealCutoff]

/-- Strictly increasing real blocks bracketed by `Q₀ < z₁ ≤ Q_t` give the exact rooted source
schedule. -/
def MTFiniteIterationSourceData.ofRootedRealSchedule {t : ℕ}
    (z₀ D : ℕ) (Q : ℕ → ℝ) (z₁ : ℝ)
    (hQnonneg : ∀ j, 0 ≤ Q j)
    (hQstrict : StrictMono Q)
    (hz₀Q : (z₀ : ℝ) ≤ Q 0)
    (hQ₀z₁ : Q 0 < z₁)
    (hz₁Qt : z₁ ≤ Q t) :
    MTFiniteIterationSourceData t := by
  apply MTFiniteIterationSourceData.ofRealAdjacentSchedule z₀ D Q
    (mtRootedRealCutoff Q z₁) hQnonneg hQstrict.monotone hz₀Q
  · intro j
    induction j using Fin.lastCases with
    | last => simpa using hz₀Q.trans hQ₀z₁.le
    | cast i =>
        simpa using hz₀Q.trans (hQstrict.monotone (Nat.zero_le i.1))
  · intro j
    induction j using Fin.lastCases with
    | last => simpa using hz₁Qt
    | cast i => simp
  · intro i
    by_cases hlast : i.succ = Fin.last t
    · rw [hlast, mtRootedRealCutoff_last]
      exact hQ₀z₁
    · have hvalLt : i.succ.1 < t := by
        have hvalLe : i.succ.1 ≤ t := by omega
        exact lt_of_le_of_ne hvalLe (by
          intro hEq
          apply hlast
          exact Fin.ext hEq)
      let k : Fin t := ⟨i.succ.1, hvalLt⟩
      have hik : i.succ = k.castSucc := Fin.ext rfl
      rw [hik, mtRootedRealCutoff_castSucc]
      exact hQstrict (by simp [k])

/-- Literal geometric level `Q_j = (1 + δ)^(start+j)`. -/
def mtGeometricLevel (δ : ℝ) (start j : ℕ) : ℝ :=
  (1 + δ) ^ (start + j)

/-- Geometric levels are strictly increasing when `δ > 0`. -/
theorem mtGeometricLevel_strictMono {δ : ℝ} (hδ : 0 < δ) (start : ℕ) :
    StrictMono (mtGeometricLevel δ start) := by
  intro i j hij
  exact pow_lt_pow_right₀ (by linarith : 1 < (1 + δ : ℝ)) (by omega)

/-- Geometric levels are positive. -/
theorem mtGeometricLevel_pos {δ : ℝ} (hδ : 0 < δ) (start j : ℕ) :
    0 < mtGeometricLevel δ start j := by
  exact pow_pos (by linarith) _

/-- Exact source data for the literal geometric blocks
`((1+δ)^(start+j),(1+δ)^(start+j+1)]`, with root cutoff `z₁`. -/
def MTFiniteIterationSourceData.ofGeometricSchedule {t : ℕ}
    (z₀ D start : ℕ) (δ z₁ : ℝ) (hδ : 0 < δ)
    (hz₀Q : (z₀ : ℝ) ≤ mtGeometricLevel δ start 0)
    (hQ₀z₁ : mtGeometricLevel δ start 0 < z₁)
    (hz₁Qt : z₁ ≤ mtGeometricLevel δ start t) :
    MTFiniteIterationSourceData t :=
  MTFiniteIterationSourceData.ofRootedRealSchedule z₀ D
    (mtGeometricLevel δ start) z₁
    (fun j => (mtGeometricLevel_pos hδ start j).le)
    (mtGeometricLevel_strictMono hδ start) hz₀Q hQ₀z₁ hz₁Qt

end

end RHTower.Sieve
