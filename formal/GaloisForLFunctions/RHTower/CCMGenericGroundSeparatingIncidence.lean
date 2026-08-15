import GaloisForLFunctions.RHTower.CCMCompressedShiftIndependence
import GaloisForLFunctions.HTGeometry.SeparatingGramLocus

/-!
# The CCM prime-channel separating locus

A bump supported in `[0, ε]` is carried by the compressed shift of label `h` into the window
`[h, h + ε]`.  When the labels are separated by more than `ε` and stay above `ε`, the windows are
pairwise disjoint, so the bump together with its shifted images is linearly independent: a
separating vector for the prime channels exists.

Distinct prime powers give distinct labels: `m log p = ℓ log q` with `m, ℓ ≥ 1` forces `p = q` and
`m = ℓ`, by rational independence of the prime logarithms.
-/

namespace GaloisForLFunctions.RHTower

open Set GaloisForLFunctions.HTGeometry

noncomputable section

/-- The bump used as the separating test vector. -/
def separatingBump (ε : ℝ) : ℝ → ℂ := fun x => if x ∈ Icc (0 : ℝ) ε then 1 else 0

theorem separatingBump_eq_zero_of_notMem {ε x : ℝ} (hx : x ∉ Icc (0 : ℝ) ε) :
    separatingBump ε x = 0 := by
  simp [separatingBump, hx]

theorem separatingBump_zero {ε : ℝ} (hε : 0 ≤ ε) : separatingBump ε 0 = 1 := by
  simp [separatingBump, hε]

/-- **The support law.**  The compressed shift of a bump lives in the shifted window. -/
theorem compressedShift_separatingBump_eq_zero {A h ε x : ℝ} (hx : x ∉ Icc h (h + ε)) :
    compressedShift A h (separatingBump ε) x = 0 := by
  rw [compressedShift_apply]
  by_cases hxA : x ∈ Icc (0 : ℝ) A
  · simp only [hxA, if_true]
    by_cases hxh : x - h ∈ Icc (0 : ℝ) A
    · simp only [hxh, if_true]
      have hnot : x - h ∉ Icc (0 : ℝ) ε := by
        intro hmem
        exact hx ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      rw [separatingBump_eq_zero_of_notMem hnot, mul_zero]
    · simp [hxh]
  · simp [hxA]

/-- The compressed shift of a bump is nonzero at the label. -/
theorem compressedShift_separatingBump_apply {A h ε : ℝ} (hε : 0 ≤ ε) (hh : h ∈ Icc (0 : ℝ) A) :
    compressedShift A h (separatingBump ε) h = (Real.exp h : ℂ) := by
  rw [compressedShift_apply]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) A := ⟨le_refl 0, le_trans hh.1 hh.2⟩
  simp [hh, sub_self, h0, separatingBump_zero hε]

/-- The bump together with its compressed shifts, indexed by `Fin (k+1)`. -/
def separatingChannels (A ε : ℝ) {k : ℕ} (h : Fin k → ℝ) : Fin (k + 1) → (ℝ → ℂ) :=
  Fin.cons (separatingBump ε) fun j => compressedShift A (h j) (separatingBump ε)

/-- The window carrying each channel. -/
def channelWindow (ε : ℝ) {k : ℕ} (h : Fin k → ℝ) : Fin (k + 1) → Set ℝ :=
  Fin.cons (Icc (0 : ℝ) ε) fun j => Icc (h j) (h j + ε)

theorem separatingChannels_eq_zero_of_notMem {A ε : ℝ} {k : ℕ} (h : Fin k → ℝ)
    (i : Fin (k + 1)) {a : ℝ} (ha : a ∉ channelWindow ε h i) :
    separatingChannels A ε h i a = 0 := by
  revert ha
  refine Fin.cases ?_ ?_ i
  · intro ha0
    simpa [separatingChannels] using
      separatingBump_eq_zero_of_notMem (by simpa [channelWindow] using ha0)
  · intro j ha0
    simpa [separatingChannels] using
      compressedShift_separatingBump_eq_zero (A := A) (by simpa [channelWindow] using ha0)

/-- Distinct channels have disjoint windows. -/
theorem channelWindow_unique {ε : ℝ} {k : ℕ} (h : Fin k → ℝ)
    (hlow : ∀ j, ε < h j) (hsep : ∀ i j, i ≠ j → ε < |h i - h j|)
    (i j : Fin (k + 1)) {a : ℝ} (hi : a ∈ channelWindow ε h i) (hj : a ∈ channelWindow ε h j) :
    i = j := by
  revert hi hj
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · intro _ _; rfl
    · intro jj hi0 hj0
      exfalso
      have h1 : a ≤ ε := (by simpa [channelWindow] using hi0 : a ∈ Icc (0 : ℝ) ε).2
      have h2 : h jj ≤ a := (by simpa [channelWindow] using hj0 : a ∈ Icc (h jj) (h jj + ε)).1
      linarith [hlow jj]
  · intro ii
    refine Fin.cases ?_ ?_ j
    · intro hi0 hj0
      exfalso
      have h1 : h ii ≤ a := (by simpa [channelWindow] using hi0 : a ∈ Icc (h ii) (h ii + ε)).1
      have h2 : a ≤ ε := (by simpa [channelWindow] using hj0 : a ∈ Icc (0 : ℝ) ε).2
      linarith [hlow ii]
    · intro jj hi0 hj0
      have hmi : a ∈ Icc (h ii) (h ii + ε) := by simpa [channelWindow] using hi0
      have hmj : a ∈ Icc (h jj) (h jj + ε) := by simpa [channelWindow] using hj0
      have hiijj : ii = jj := by
        by_contra hcon
        have hs := hsep ii jj hcon
        rcases abs_cases (h ii - h jj) with ⟨heq, _⟩ | ⟨heq, _⟩ <;> rw [heq] at hs <;>
          linarith [hmi.1, hmi.2, hmj.1, hmj.2]
      rw [hiijj]

/-- **Equation (8).**  With labels separated by more than the bump width and bounded away from the
origin, the channel family is linearly independent: a separating vector exists. -/
theorem linearIndependent_separatingChannels {A ε : ℝ} {k : ℕ} (h : Fin k → ℝ)
    (hε : 0 < ε) (hlow : ∀ j, ε < h j) (hhigh : ∀ j, h j + ε ≤ A)
    (hsep : ∀ i j, i ≠ j → ε < |h i - h j|) :
    LinearIndependent ℂ (separatingChannels A ε h) := by
  classical
  refine linearIndependent_of_disjoint_support _ ?_ ?_
  · intro i
    refine Fin.cases ?_ ?_ i
    · exact ⟨0, by simp [separatingChannels, separatingBump_zero hε.le]⟩
    · intro j
      refine ⟨h j, ?_⟩
      have hmem : h j ∈ Icc (0 : ℝ) A :=
        ⟨le_of_lt (lt_trans hε (hlow j)), le_trans (by linarith [hε.le]) (hhigh j)⟩
      have hval : separatingChannels A ε h j.succ (h j) = (Real.exp (h j) : ℂ) := by
        simpa [separatingChannels] using
          compressedShift_separatingBump_apply (A := A) (h := h j) hε.le hmem
      rw [hval]
      exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  · intro i j hij a
    by_cases hi : a ∈ channelWindow ε h i
    · right
      refine separatingChannels_eq_zero_of_notMem h j (fun hj => hij ?_)
      exact channelWindow_unique h hlow hsep i j hi hj
    · left
      exact separatingChannels_eq_zero_of_notMem h i hi

/-! ## Distinct prime-power labels -/

/-- **Equation (10f).**  Distinct prime powers give distinct shift labels. -/
theorem primePowerLabel_inj {p q : Nat.Primes} {m l : ℕ} (hm : 0 < m)
    (hlab : (m : ℝ) * Real.log ((p : ℕ) : ℝ) = (l : ℝ) * Real.log ((q : ℕ) : ℝ)) :
    p = q ∧ m = l := by
  classical
  by_cases hpq : p = q
  · refine ⟨hpq, ?_⟩
    subst hpq
    have hlogpos : 0 < Real.log ((p : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast p.2.one_lt)
    have hmr : (m : ℝ) = (l : ℝ) := mul_right_cancel₀ (ne_of_gt hlogpos) hlab
    exact_mod_cast hmr
  · exfalso
    have hinj : Function.Injective (![p, q] : Fin 2 → Nat.Primes) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    have hpair : LinearIndependent ℚ ![Real.log ((p : ℕ) : ℝ), Real.log ((q : ℕ) : ℝ)] := by
      have hcomp := GaloisForLFunctions.linearIndependent_log_primes.comp _ hinj
      have heq : ((fun r : Nat.Primes => Real.log ((r : ℕ) : ℝ)) ∘ (![p, q] : Fin 2 → Nat.Primes))
          = ![Real.log ((p : ℕ) : ℝ), Real.log ((q : ℕ) : ℝ)] := by
        funext i
        fin_cases i <;> simp
      rw [← heq]
      exact hcomp
    have hzero : (m : ℚ) • Real.log ((p : ℕ) : ℝ) + (-(l : ℚ)) • Real.log ((q : ℕ) : ℝ) = 0 := by
      simp only [Rat.smul_def]
      push_cast
      linarith [hlab]
    have hcoeff := (LinearIndependent.pair_iff.1 hpair) _ _ hzero
    have hm0 : (m : ℚ) = 0 := hcoeff.1
    have hmz : m = 0 := by exact_mod_cast hm0
    omega

end

end GaloisForLFunctions.RHTower
