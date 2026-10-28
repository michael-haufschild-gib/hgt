import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheAtomicFormIsMetzlerBelowTheSpacing
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheSignIsAGaugeFixing

/-!
# The atomic Metzler property is selective

Below the spacing the Euler-gauge atomic intersection Gram of `ζ` is Metzler
(`TheAtomicFormIsMetzlerBelowTheSpacing`). For a real twin `ω` of the prime place the atom block is
`−M^ω` with the twisted prime pairing `Σ_k ω(k)Λ_k(·)`. This file shows that the sign hypothesis
selects the Euler point on the actual atomic family.

* **The pole row fixes the gauge** (`gauge_eq_of_poleRow`): the pairings `∫ g_n e^{−u/2}` are
  positive and the pole plane is untouched by the twist, so a nonnegative unimodular gauge is
  constant on the atoms.
* **The pair `(1, p)` carries the twist** (`twinMarkovPair_one_prime`): for separated atoms only the
  lag `log p` meets the pair, so the twisted prime pairing is exactly `ω(p) (log p/√p) ‖g‖²`, while
  the Lévy cross energy is at most `2w ω(log p − w) ‖g‖²` (`levyCross_one_prime_le`).
* **Selectivity** (`not_exists_nonneg_gauge_twinAtomicIntersectionGram`): if `ω(p) = −1` for a
  prime `p ≤ N` and `2w ω(log p − w) < log p/√p`, the twin's atomic intersection Gram admits no
  unimodular gauge with nonnegative off-diagonal entries. With `ω ≡ 1` it is Metzler.

So below the spacing the Lorentzian sign hypothesis holds for `ζ` and fails, in every gauge, for
every twin that flips a prime of the horizon: the selection of the Euler point is performed by the
pole row and the archimedean place, as in `TheSignIsAGaugeFixing`.
-/

noncomputable section

open MeasureTheory Set Finset Matrix RHTower Complex
open scoped Real ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### The twisted Markov pairing and the twin's Gram -/

/-- The prime pairing twisted by `ω`: `Σ_k ω(k)Λ_k (∫ f d(· − log k) + ∫ f d(· + log k))`. -/
def twinPrimePair (ω : ℕ → ℝ) (f d : ℝ → ℝ) : ℝ :=
  ∑' k : ℕ, ω k * vonMangoldtAtom k *
    ((∫ t, f t * d (t - Real.log k)) + ∫ t, f t * d (t + Real.log k))

/-- The twin's Markov pairing. -/
def twinMarkovPair (ω : ℕ → ℝ) (f d : ℝ → ℝ) : ℝ :=
  2 * gammaHardyPhaseRate 0 * (∫ u, f u * d u) + (∫ y in Ioi 0, levyMixed f d y) -
    twinPrimePair ω f d

/-- The twin's atomic Markov Gram. -/
def twinMarkovGram (ω : ℕ → ℝ) (g : ℝ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => twinMarkovPair ω (atom g ((i : ℕ) + 1)) (atom g ((j : ℕ) + 1))

/-- The twin's atomic intersection Gram: the pole plane and pole row are those of `ζ`. -/
def twinAtomicIntersectionGram (ω : ℕ → ℝ) (g : ℝ → ℝ) (N : ℕ) :
    Matrix (Fin 2 ⊕ Fin N) (Fin 2 ⊕ Fin N) ℝ :=
  fromBlocks realPolePlane (atomPoleRow g N) (atomPoleRow g N)ᵀ (-twinMarkovGram ω g N)

theorem twinMarkovPair_one (f d : ℝ → ℝ) : twinMarkovPair (fun _ => 1) f d = markovPair f d := by
  simp [twinMarkovPair, markovPair, twinPrimePair, primePair]

/-! ### The pole row fixes the gauge -/

/-- **The pole row fixes the gauge**: a unimodular gauge making the positive `H`-row nonnegative is
constant on the atoms. -/
theorem gauge_eq_of_poleRow (hg : Continuous g) (hgc : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u)
    {u₀ : ℝ} (hu₀ : 0 < g u₀) {N : ℕ} {G : Matrix (Fin 2 ⊕ Fin N) (Fin 2 ⊕ Fin N) ℝ}
    (hG : ∀ j, G (Sum.inl 0) (Sum.inr j) = atomPoleRow g N 0 j) {γ : Fin 2 ⊕ Fin N → ℂ}
    (hγ : ∀ i, ‖γ i‖ = 1)
    (hnn : ∀ i j, i ≠ j → 0 ≤ conj (γ i) * γ j * ((G i j : ℝ) : ℂ)) (j : Fin N) :
    γ (Sum.inr j) = γ (Sum.inl 0) := by
  have h := hnn (Sum.inl 0) (Sum.inr j) (by simp)
  rw [hG] at h
  exact (eq_of_conj_mul_nonneg (hγ _) (hγ _) (atomPoleRow_zero_pos hg hgc hg0 hu₀ j) h).symm

/-! ### The pair `(1, p)` -/

theorem archLevyDensity_antitone {y₁ y₂ : ℝ} (h0 : 0 < y₁) (h12 : y₁ ≤ y₂) :
    archLevyDensity y₂ ≤ archLevyDensity y₁ := by
  unfold archLevyDensity
  have e1 : Real.exp (-y₂ / 2) ≤ Real.exp (-y₁ / 2) := Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp (-2 * y₂) ≤ Real.exp (-2 * y₁) := Real.exp_le_exp.mpr (by linarith)
  have d1 : 0 < 1 - Real.exp (-2 * y₁) := by
    have := Real.exp_lt_one_iff.mpr (by linarith : -2 * y₁ < 0); linarith
  exact div_le_div₀ (Real.exp_pos _).le e1 d1 (by linarith)

theorem atom_one (g : ℝ → ℝ) : atom g 1 = g := by funext u; simp [atom]

/-- The bump of the atom `p` vanishes against the atom `1` unless the lag is `log p`. -/
theorem mul_atom_eq_zero_of_far (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {c : ℝ}
    (hc : w < |c|) (t : ℝ) : g t * g (t + c) = 0 := by
  by_cases ht : t ∈ Set.Icc 0 w
  · have : t + c ∉ Set.Icc 0 w := fun h => by
      have : |c| ≤ w := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2, h.1, h.2]
      linarith
    rw [hgsupp _ this, mul_zero]
  · rw [hgsupp t ht, zero_mul]

/-- **The twisted prime pairing of `(1, p)` is `ω(p) (log p/√p) ‖g‖²`** for separated atoms. -/
theorem twinPrimePair_one_prime (ω : ℕ → ℝ) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) (hw : w < atomSpacing N) :
    twinPrimePair ω (atom g 1) (atom g p) = ω p * vonMangoldtAtom p * ∫ t, g t ^ 2 := by
  have hp2 := hp.two_le
  have hN1 : 1 ≤ N := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
  have hwl2 : w < Real.log 2 := lt_of_lt_of_le hw (atomSpacing_le_log_two hN1)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [atom_one, twinPrimePair, tsum_eq_single p]
  · -- at `k = p`: the `−` lag misses, the `+` lag is the overlap `‖g‖²`
    have h1 : ∫ t, g t * atom g p (t - Real.log p) = 0 := by
      have hlp : w < |-(2 * Real.log p)| := by
        rw [abs_neg, abs_of_pos (by linarith)]; linarith
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
      have := mul_atom_eq_zero_of_far hgsupp hlp t
      simp only [atom, Pi.zero_apply]
      rw [show t - Real.log p - Real.log p = t + -(2 * Real.log p) by ring]
      exact this
    have h2 : ∫ t, g t * atom g p (t + Real.log p) = ∫ t, g t ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun t => by simp [atom, sq])
    rw [h1, h2, zero_add]
  · -- every other lag misses the pair
    intro k hk
    by_cases hk2 : 2 ≤ k
    · have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
      have hkp : w < |Real.log k - Real.log p| := by
        rcases lt_or_gt_of_ne hk with hlt | hgt
        · have := atomSpacing_le_abs_logGap (N := N) (m := k) (n := p)
            (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (Finset.mem_Icc.mpr ⟨by omega, hpN⟩)
            (by omega)
          rw [logGap, abs_sub_comm] at this; linarith
        · have hsp : atomSpacing N ≤ Real.log k - Real.log p := by
            rw [← Real.log_div hk0.ne' hp0.ne', atomSpacing]
            refine Real.log_le_log (by positivity) ?_
            rw [le_div_iff₀ hp0]
            have h1 : (p : ℝ) + 1 ≤ k := by exact_mod_cast hgt
            have h2 : (p : ℝ) ≤ N := by exact_mod_cast hpN
            have h3 : (1 + 1 / (N : ℝ)) * p = p + p / N := by ring
            have h4 : (p : ℝ) / N ≤ 1 := by rw [div_le_one hNr]; exact h2
            linarith
          rw [abs_of_pos (by linarith [atomSpacing_pos hN1])]
          linarith
      have hz1 : ∀ t, g t * atom g p (t - Real.log k) = 0 := fun t => by
        simp only [atom]
        rw [show t - Real.log k - Real.log p = t + -(Real.log k + Real.log p) by ring]
        refine mul_atom_eq_zero_of_far hgsupp ?_ t
        rw [abs_neg, abs_of_pos (by linarith)]
        linarith
      have hz2 : ∀ t, g t * atom g p (t + Real.log k) = 0 := fun t => by
        simp only [atom]
        rw [show t + Real.log k - Real.log p = t + (Real.log k - Real.log p) by ring]
        exact mul_atom_eq_zero_of_far hgsupp hkp t
      simp [hz1, hz2]
    · simp [vonMangoldtAtom, hk2]

/-- **The Lévy cross energy of `(1, p)` is small**: `∫ levyMixed ≥ −2w ω(log p − w) ‖g‖²`. -/
theorem levyCross_one_prime_le (hg : Continuous g) (hgc : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 ≤ w) {p : ℕ}
    (hwp : w < Real.log p) :
    -(2 * w * archLevyDensity (Real.log p - w) * ∫ t, g t ^ 2) ≤
      ∫ y in Ioi 0, levyMixed (atom g 1) (atom g p) y := by
  set lp := Real.log p
  set C := archLevyDensity (lp - w) * ∫ t, g t ^ 2
  set W := Set.Icc (lp - w) (lp + w)
  -- the cross integrand is `−ω(y) G(y − log p)`
  have hG : ∀ y, 0 < y → levyMixed (atom g 1) (atom g p) y =
      -(archLevyDensity y * ∫ u, g u * g (u + (y - lp))) := fun y hy => by
    unfold levyMixed
    rw [atom_one, ← mul_neg, ← integral_neg]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have h1 : g u * g (u - lp) = 0 := by
      rw [show u - lp = u + -lp by ring]
      exact mul_atom_eq_zero_of_far hgsupp (by rw [abs_neg, abs_of_pos (by linarith)]; exact hwp) u
    have h2 : g (u + y) * g (u + y - lp) = 0 := by
      rw [show u + y - lp = (u + y) + -lp by ring]
      exact mul_atom_eq_zero_of_far hgsupp (by rw [abs_neg, abs_of_pos (by linarith)]; exact hwp) _
    have h3 : g (u + y) * g (u - lp) = 0 := by
      rw [show u - lp = (u + y) + -(y + lp) by ring]
      exact mul_atom_eq_zero_of_far hgsupp (by rw [abs_neg, abs_of_pos (by linarith)]; linarith) _
    simp only [atom]
    rw [show u + y - lp = u + (y - lp) by ring] at h2 ⊢
    nlinarith [h1, h2, h3]
  -- `0 ≤ ω(y) G(y − log p) ≤ C 𝟙_W(y)` on `(0, ∞)`
  have hF0 : ∀ y, 0 < y → 0 ≤ archLevyDensity y * ∫ u, g u * g (u + (y - lp)) := fun y hy =>
    mul_nonneg (archLevyDensity_pos hy).le (integral_nonneg fun u => mul_nonneg (hg0 _) (hg0 _))
  have hFC : ∀ y, 0 < y → archLevyDensity y * ∫ u, g u * g (u + (y - lp)) ≤
      W.indicator (fun _ => C) y := fun y hy => by
    by_cases hyW : y ∈ W
    · rw [Set.indicator_of_mem hyW]
      have hcs := abs_integral_mul_shift_le hg hgc hg hgc (y - lp)
      rw [← sq, Real.sq_sqrt (integral_nonneg fun t => sq_nonneg _)] at hcs
      have hω := archLevyDensity_antitone (by linarith) hyW.1
      exact mul_le_mul hω (le_trans (le_abs_self _) hcs)
        (integral_nonneg fun u => mul_nonneg (hg0 _) (hg0 _))
        (archLevyDensity_pos (by linarith)).le
    · rw [Set.indicator_of_notMem hyW]
      have : ∫ u, g u * g (u + (y - lp)) = 0 := by
        refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
        refine mul_atom_eq_zero_of_far hgsupp ?_ u
        by_contra h; push Not at h
        exact hyW ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
      rw [this, mul_zero]
  have hC0 : 0 ≤ C := mul_nonneg (archLevyDensity_pos (by linarith)).le
    (integral_nonneg fun t => sq_nonneg _)
  have hint : Integrable (W.indicator fun _ => C) :=
    (integrableOn_const (C := C) (by simp [W])).integrable_indicator measurableSet_Icc
  have hbound : ∫ y in Ioi 0, archLevyDensity y * ∫ u, g u * g (u + (y - lp)) ≤
      2 * w * C := by
    calc ∫ y in Ioi 0, archLevyDensity y * ∫ u, g u * g (u + (y - lp))
        ≤ ∫ y in Ioi 0, W.indicator (fun _ => C) y :=
          integral_mono_of_nonneg ((ae_restrict_mem measurableSet_Ioi).mono fun y hy => hF0 y hy)
            hint.integrableOn ((ae_restrict_mem measurableSet_Ioi).mono fun y hy => hFC y hy)
      _ ≤ ∫ y, W.indicator (fun _ => C) y :=
          setIntegral_le_integral hint (Filter.Eventually.of_forall fun y =>
            Set.indicator_nonneg (fun _ _ => hC0) y)
      _ = 2 * w * C := by
          rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, measureReal_def,
            Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
          ring
  rw [setIntegral_congr_fun measurableSet_Ioi fun y hy => hG y hy, integral_neg]
  have : 2 * w * archLevyDensity (lp - w) * ∫ t, g t ^ 2 = 2 * w * C := by simp only [C]; ring
  linarith

/-- **The twin entry of `(1, p)`**: `−M^ω(g_1, g_p) ≤ (2w ω(log p − w) + ω(p) Λ_p) ‖g‖²`. -/
theorem neg_twinMarkovPair_one_prime_le (ω : ℕ → ℝ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw0 : 0 ≤ w) {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) (hw : w < atomSpacing N) :
    -twinMarkovPair ω (atom g 1) (atom g p) ≤
      (2 * w * archLevyDensity (Real.log p - w) + ω p * vonMangoldtAtom p) * ∫ t, g t ^ 2 := by
  have hp2 := hp.two_le
  have hwp : w < Real.log p := by
    have h1 := atomSpacing_le_log_two (N := N) (by omega)
    have h2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
    linarith
  -- disjoint supports: the overlap vanishes
  have h0 : ∫ u, atom g 1 u * atom g p u = 0 := by
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [atom, Nat.cast_one, Real.log_one, sub_zero, Pi.zero_apply]
    rw [show u - Real.log p = u + -Real.log p by ring]
    exact mul_atom_eq_zero_of_far hgsupp (by rw [abs_neg, abs_of_pos (by linarith)]; exact hwp) u
  have hL := levyCross_one_prime_le hg hgc hg0 hgsupp hw0 hwp
  have hP := twinPrimePair_one_prime ω hgsupp hp hpN hw
  unfold twinMarkovPair
  rw [h0, mul_zero, zero_add, hP]
  nlinarith

/-! ### Selectivity -/

theorem twinAtomicIntersectionGram_one (g : ℝ → ℝ) (N : ℕ) :
    twinAtomicIntersectionGram (fun _ => 1) g N = atomicIntersectionGram g N := by
  unfold twinAtomicIntersectionGram atomicIntersectionGram twinMarkovGram atomicMarkovGram
  simp only [twinMarkovPair_one]

/-- **The atomic Metzler property is selective.** Below the spacing, a real twin with `ω(p) = −1`
at a prime `p ≤ N` (and `2w ω(log p − w) < Λ(p)/√p`) has an atomic intersection Gram with no
unimodular gauge making its off-diagonal entries nonnegative; for `ω ≡ 1` the Gram is Metzler. -/
theorem not_exists_nonneg_gauge_twinAtomicIntersectionGram (ω : ℕ → ℝ) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {u₀ : ℝ} (hu₀ : 0 < g u₀) (hw0 : 0 ≤ w) {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    (hw : w < atomSpacing N) (hωp : ω p = -1)
    (hwin : 2 * w * archLevyDensity (Real.log p - w) < vonMangoldtAtom p) :
    ¬ ∃ γ : Fin 2 ⊕ Fin N → ℂ, (∀ i, ‖γ i‖ = 1) ∧
      ∀ i j, i ≠ j → 0 ≤ conj (γ i) * γ j * ((twinAtomicIntersectionGram ω g N i j : ℝ) : ℂ) := by
  rintro ⟨γ, hγ, hnn⟩
  have hp2 := hp.two_le
  have hconst := gauge_eq_of_poleRow hg.continuous hgc hg0 hu₀
    (G := twinAtomicIntersectionGram ω g N) (fun j => by simp [twinAtomicIntersectionGram]) hγ hnn
  set j1 : Fin N := ⟨0, by omega⟩
  set jp : Fin N := ⟨p - 1, by omega⟩
  have hne : (Sum.inr j1 : Fin 2 ⊕ Fin N) ≠ Sum.inr jp := by
    simp only [ne_eq, Sum.inr.injEq, j1, jp, Fin.ext_iff]; omega
  have h := hnn _ _ hne
  rw [hconst j1, hconst jp] at h
  have hc : conj (γ (Sum.inl 0)) * γ (Sum.inl 0) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hγ]; simp
  rw [hc, one_mul, Complex.zero_le_real] at h
  have hentry : twinAtomicIntersectionGram ω g N (Sum.inr j1) (Sum.inr jp) =
      -twinMarkovPair ω (atom g 1) (atom g p) := by
    simp only [twinAtomicIntersectionGram, fromBlocks_apply₂₂, Matrix.neg_apply, twinMarkovGram,
      Matrix.of_apply, j1, jp, zero_add, Nat.sub_add_cancel hp.one_lt.le]
  rw [hentry] at h
  have hle := neg_twinMarkovPair_one_prime_le ω hg.continuous hgc hg0 hgsupp hw0 hp hpN hw
  have hg2 : 0 < ∫ u, g u ^ 2 := by
    have hgc2 : HasCompactSupport fun u => g u ^ 2 := by
      rw [show (fun u => g u ^ 2) = g * g from funext fun u => by simp [sq]]
      exact hgc.mul_right
    exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := u₀)
      (hg.continuous.pow 2) hgc2 (fun u => sq_nonneg _) (pow_ne_zero 2 hu₀.ne')
  rw [hωp] at hle
  have : (2 * w * archLevyDensity (Real.log p - w) + -1 * vonMangoldtAtom p) * ∫ t, g t ^ 2 < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hg2
  linarith

end GaloisForLFunctions.ArithmeticLorentzianGeometry
