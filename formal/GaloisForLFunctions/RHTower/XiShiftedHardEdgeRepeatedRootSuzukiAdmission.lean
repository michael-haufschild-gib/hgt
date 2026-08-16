import GaloisForLFunctions.RHTower.XiShiftedHardEdgeOddRootSuzukiAdmission

/-!
# Route U repeated-root descendants in Suzuki's critical form domain

A symmetric root pair of multiplicity `m` produces `m` successive even quotients and their odd
twins.  The one-step compact division theorem did not by itself justify iteration: its factor law
degenerates at the two roots and therefore did not show that the first quotient retains the next
copy of the root.  Continuity closes exactly that gap.

This file iterates the compact division at unchanged time aperture.  At every depth `k ≤ m`, the
time source remains integrable and compactly supported and its real-frequency transform is exactly
the residual factor `(w²-c²)^(m-k) G(w)`.  Consequently every odd twin through terminal depth is
an actual vector in Suzuki's exact logarithmic form domain at that same aperture.
-/

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform

noncomputable section

namespace RHTower

/-- Iterate compact division by the symmetric pair `±c`, without changing time support. -/
def routeURealRepeatedRootDividedTime (b c : ℝ) (h : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => h
  | k + 1 => routeURealTwiceRootDividedTime b c
      (routeURealRepeatedRootDividedTime b c h k)

/-- At every permitted division depth, compact support and integrability survive and the exact
residual multiplicity is visible pointwise, including at `±c`. -/
theorem routeURealRepeatedRootDividedTime_invariants
    (a : SuzukiPositiveAperture) {c : ℝ} {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc0 : c ≠ 0) (m : ℕ) {G : ℝ → ℂ} (hG : Continuous G)
    (hfactor : ∀ w : ℝ, routeURealFourier h w =
      (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ m) * G w) :
    ∀ k : ℕ, k ≤ m →
      Integrable (routeURealRepeatedRootDividedTime (-a.1) c h k) ∧
      (∀ y, y ≤ -a.1 ∨ a.1 ≤ y →
        routeURealRepeatedRootDividedTime (-a.1) c h k y = 0) ∧
      (∀ w : ℝ,
        routeURealFourier (routeURealRepeatedRootDividedTime (-a.1) c h k) w =
          (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ (m - k)) * G w) := by
  intro k hk
  induction k with
  | zero =>
      exact ⟨hh, hsupp, by
        simpa [routeURealRepeatedRootDividedTime] using hfactor⟩
  | succ k ih =>
      have hklt : k < m := Nat.lt_of_succ_le hk
      obtain ⟨hq1, hqsupp, hqfactor⟩ := ih (Nat.le_of_lt hklt)
      have hpow : m - k = (m - (k + 1)) + 1 := by omega
      have hqc : routeURealFourier
          (routeURealRepeatedRootDividedTime (-a.1) c h k) c = 0 := by
        rw [hqfactor c]
        simp [hpow]
      have hqnegc : routeURealFourier
          (routeURealRepeatedRootDividedTime (-a.1) c h k) (-c) = 0 := by
        rw [hqfactor (-c)]
        simp [hpow]
      have hbd : -a.1 ≤ a.1 := by linarith [a.2]
      have hqfactor' : ∀ w : ℝ,
          routeURealFourier
              (routeURealRepeatedRootDividedTime (-a.1) c h k) w =
            (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ ((m - (k + 1)) + 1)) * G w := by
        simpa only [hpow] using hqfactor
      refine ⟨?_, ?_, ?_⟩
      · simpa [routeURealRepeatedRootDividedTime] using
          integrable_routeURealTwiceRootDividedTime
            hbd hq1 hqsupp hqc hqnegc hc0
      · simpa [routeURealRepeatedRootDividedTime] using
          routeURealTwiceRootDividedTime_support
            hbd hq1 hqsupp hqc hqnegc hc0
      · simpa [routeURealRepeatedRootDividedTime] using
          routeURealTwiceRootDividedTime_fourier_factor_pow
            hbd hq1 hqsupp hqc hqnegc hc0 (m - (k + 1)) hG hqfactor'

/-- Before each division step, the residual source still vanishes at both selected roots. -/
theorem routeURealRepeatedRootDividedTime_zero_at_roots
    (a : SuzukiPositiveAperture) {c : ℝ} {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc0 : c ≠ 0) (m : ℕ) {G : ℝ → ℂ} (hG : Continuous G)
    (hfactor : ∀ w : ℝ, routeURealFourier h w =
      (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ m) * G w)
    {k : ℕ} (hk : k < m) :
    routeURealFourier (routeURealRepeatedRootDividedTime (-a.1) c h k) c = 0 ∧
      routeURealFourier (routeURealRepeatedRootDividedTime (-a.1) c h k) (-c) = 0 := by
  obtain ⟨_, _, hqfactor⟩ := routeURealRepeatedRootDividedTime_invariants
    a hh hsupp hc0 m hG hfactor k (Nat.le_of_lt hk)
  have hpow0 : m - k ≠ 0 := by omega
  constructor
  · rw [hqfactor c]
    simp [hpow0]
  · rw [hqfactor (-c)]
    simp [hpow0]

/-- **All repeated-root even descendants are admitted at unchanged aperture.**  Every nonzero
division depth has an exact Suzuki form vector whose unweighted Fourier component is the Fourier
transform of the corresponding compact quotient. -/
theorem exists_routeURealRepeatedRootEvenSuzukiAdmission
    (a : SuzukiPositiveAperture) {c : ℝ} {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc0 : c ≠ 0) (m : ℕ) {G : ℝ → ℂ} (hG : Continuous G)
    (hfactor : ∀ w : ℝ, routeURealFourier h w =
      (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ m) * G w)
    {k : ℕ} (hk : k < m) :
    let q := routeURealRepeatedRootDividedTime (-a.1) c h (k + 1)
    ∃ (hq2 : MemLp q 2 (volume : Measure ℝ))
        (v : SuzukiHlogFormDomain a),
      suzukiHlogWeightedToL2 v.1 = fourierUnitary (hq2.toLp q) ∧
      ∀ w : ℝ, routeURealFourier q w =
        (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ (m - (k + 1))) * G w := by
  dsimp only
  obtain ⟨hprev1, hprevsupp, _⟩ := routeURealRepeatedRootDividedTime_invariants
    a hh hsupp hc0 m hG hfactor k (Nat.le_of_lt hk)
  obtain ⟨hprevc, hprevnegc⟩ := routeURealRepeatedRootDividedTime_zero_at_roots
    a hh hsupp hc0 m hG hfactor hk
  have hbd : -a.1 ≤ a.1 := by linarith [a.2]
  let q := routeURealRepeatedRootDividedTime (-a.1) c h (k + 1)
  let hq2 : MemLp q 2 (volume : Measure ℝ) := by
    simpa [q, routeURealRepeatedRootDividedTime] using
      memLp_routeURealTwiceRootDividedTime
        hbd hprev1 hprevsupp hprevc hprevnegc hc0
  let v : SuzukiHlogFormDomain a :=
    routeURealTwiceRootDividedSuzukiFormVector a c
      (routeURealRepeatedRootDividedTime (-a.1) c h k)
      hprev1 hprevsupp hprevc hprevnegc hc0
  refine ⟨hq2, v, ?_, ?_⟩
  · rw [← fourierUnitary_suzukiHlogFourierToTime v.1]
    change fourierUnitary (suzukiHlogFormEmbedding a v) =
      fourierUnitary (hq2.toLp q)
    congr 1
    simpa [v, q, hq2, routeURealRepeatedRootDividedTime] using
      suzukiHlogFormEmbedding_routeURealTwiceRootDividedSuzukiFormVector
        a c (routeURealRepeatedRootDividedTime (-a.1) c h k)
          hprev1 hprevsupp hprevc hprevnegc hc0
  · exact (routeURealRepeatedRootDividedTime_invariants
      a hh hsupp hc0 m hG hfactor (k + 1) (Nat.succ_le_iff.mpr hk)).2.2

/-- **All repeated-root odd twins are admitted at unchanged aperture.**  At every depth before
the multiplicity is exhausted, the compact division source produces an exact Suzuki form vector.
Its unweighted Fourier component is the Fourier transform of the literal compact odd descendant,
and that descendant has the expected residual factor pointwise. -/
theorem exists_routeURealRepeatedRootOddSuzukiAdmission
    (a : SuzukiPositiveAperture) {c : ℝ} {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc0 : c ≠ 0) (m : ℕ) {G : ℝ → ℂ} (hG : Continuous G)
    (hfactor : ∀ w : ℝ, routeURealFourier h w =
      (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ m) * G w)
    {k : ℕ} (hk : k < m) :
    let q := routeURealRepeatedRootDividedTime (-a.1) c h k
    let odd := routeURealOddRootDividedTime (-a.1) c q
    ∃ (hodd2 : MemLp odd 2 (volume : Measure ℝ))
        (v : SuzukiHlogFormDomain a),
      suzukiHlogWeightedToL2 v.1 = fourierUnitary (hodd2.toLp odd) ∧
      ∀ w : ℝ, routeURealFourier odd w =
        (w : ℂ) * (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ (m - (k + 1))) * G w := by
  dsimp only
  obtain ⟨hq1, hqsupp, _⟩ := routeURealRepeatedRootDividedTime_invariants
    a hh hsupp hc0 m hG hfactor k (Nat.le_of_lt hk)
  obtain ⟨hqc, hqnegc⟩ := routeURealRepeatedRootDividedTime_zero_at_roots
    a hh hsupp hc0 m hG hfactor hk
  have hbd : -a.1 ≤ a.1 := by linarith [a.2]
  let odd := routeURealOddRootDividedTime (-a.1) c
    (routeURealRepeatedRootDividedTime (-a.1) c h k)
  let hodd2 : MemLp odd 2 (volume : Measure ℝ) :=
    memLp_routeURealOddRootDividedTime hbd hq1 hqsupp hqc hqnegc hc0
  let v : SuzukiHlogFormDomain a :=
    routeURealOddRootDividedSuzukiFormVector a c
      (routeURealRepeatedRootDividedTime (-a.1) c h k)
      hq1 hqsupp hqc hqnegc hc0
  refine ⟨hodd2, v, ?_, ?_⟩
  · rw [← fourierUnitary_suzukiHlogFourierToTime v.1]
    change fourierUnitary (suzukiHlogFormEmbedding a v) =
      fourierUnitary (hodd2.toLp odd)
    congr 1
    simpa [v, odd, hodd2] using
      suzukiHlogFormEmbedding_routeURealOddRootDividedSuzukiFormVector
        a c (routeURealRepeatedRootDividedTime (-a.1) c h k)
          hq1 hqsupp hqc hqnegc hc0
  · intro w
    have hnext := routeURealRepeatedRootDividedTime_invariants
      a hh hsupp hc0 m hG hfactor (k + 1) (Nat.succ_le_iff.mpr hk)
    have hodd := routeURealOddRootDividedTime_fourier_eq_mul_twice
      hbd hq1 hqsupp hqc hqnegc hc0 w
    rw [hodd]
    rw [show routeURealTwiceRootDividedTime (-a.1) c
        (routeURealRepeatedRootDividedTime (-a.1) c h k) =
          routeURealRepeatedRootDividedTime (-a.1) c h (k + 1) by rfl]
    rw [hnext.2.2 w]
    ring

end RHTower
