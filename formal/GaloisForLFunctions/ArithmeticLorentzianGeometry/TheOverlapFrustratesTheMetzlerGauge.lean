import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheAtomicFormIsMetzlerBelowTheSpacing
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheSignIsAGaugeFixing
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomHasConstantOne

/-!
# Overlap frustrates the Metzler gauge

Below the spacing the atomic intersection form of `ζ` is Metzler
(`TheAtomicFormIsMetzlerBelowTheSpacing`). Beyond it the sign of the atom block changes: two atoms
of a narrow bump `g` at log-distance `s` much smaller than the width meet with **positive** Markov
pairing, because `g + g(· − s)` is again a narrow bump, whose archimedean self-energy
`≈ log(1/w)‖g‖²` dominates, while `g − g(· − s)` is small in the Lévy norm.

* **Close atoms meet positively** (`markovPair_shift_pos`): for a nonnegative `K`-Lipschitz `C²`
  bump supported in `[0, w]` with `2w < log 2` and `κ = 2θ′(0) + log(1/(2w)) > 0`, and `0 < s ≤ w`,

      4e^{1/2}K²w²·s + 2wK²(2 log(1/w) + C₁ + 2|θ′(0)|)·s² < κ ‖g‖²

  implies `M(g, g(· − s)) > 0`. The proof is the polarization
  `4M(a, b) = M(a + b) − M(a − b)` with the self-energy bound for the bump `a + b` of width `2w` and
  the Lipschitz Lévy bound for `a − b`; no prime lag meets a window shorter than `log 2`.
* **A negative triangle admits no nonnegative gauge** (`not_nonneg_gauge_of_neg_triangle`): if
  three entries `K_ab, K_bc, K_ac` of a real kernel are negative, no unimodular phases make all three
  `conj g_i g_j K_ij` nonnegative, since each would force `g_j = −g_i`.
* **Beyond the spacing the atomic form is frustrated** (`atomicMarkovGram_frustrated`): when the
  gap `log N − log(N − 2)` satisfies the criterion, the atoms `N − 2, N − 1, N` form a negative
  triangle of `−M`, so no gauge makes the atom block Metzler. At fixed width this holds for every
  large `N` (`atomicMarkovGram_frustrated_eventually`). For a dilated bump `g₁(·/w)` the criterion
  is scale-covariant (Lipschitz constant `∝ 1/w`, `‖g‖² ∝ w`), so it also applies at every
  sufficiently large fixed overlap ratio once `log(1/w)` is large.

So the Metzler property, a theorem below the spacing, fails beyond it in every gauge: a
trickle-down proof at unbounded overlap cannot use atomic coordinates.
-/

noncomputable section

open MeasureTheory Set Finset Matrix RHTower Complex
open scoped Real ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

/-! ### A negative triangle admits no nonnegative gauge -/

/-- **Frustration.** Three negative entries `K_ab, K_bc, K_ac` admit no unimodular gauge making all
three nonnegative. -/
theorem not_nonneg_gauge_of_neg_triangle {Kab Kbc Kac : ℝ} (hab : Kab < 0) (hbc : Kbc < 0)
    (hac : Kac < 0) {ga gb gc : ℂ} (ha : ‖ga‖ = 1) (hb : ‖gb‖ = 1) (hc : ‖gc‖ = 1) :
    ¬ (0 ≤ conj ga * gb * (Kab : ℂ) ∧ 0 ≤ conj gb * gc * (Kbc : ℂ) ∧
      0 ≤ conj ga * gc * (Kac : ℂ)) := by
  rintro ⟨h1, h2, h3⟩
  -- `conj g_i g_j K = conj g_i (−g_j) |K|`, so `g_i = −g_j`
  have flip : ∀ {gi gj : ℂ} {K : ℝ}, ‖gi‖ = 1 → ‖gj‖ = 1 → K < 0 →
      0 ≤ conj gi * gj * (K : ℂ) → gi = -gj := fun {gi gj K} hi hj hK h => by
    have e : conj gi * gj * (K : ℂ) = conj gi * (-gj) * ((-K : ℝ) : ℂ) := by push_cast; ring
    rw [e] at h
    exact eq_of_conj_mul_nonneg hi (by rw [norm_neg, hj]) (by linarith) h
  have e1 := flip ha hb hab h1
  have e2 := flip hb hc hbc h2
  have e3 := flip ha hc hac h3
  have h : gc = -gc := by rw [← e3, e1, e2, neg_neg]
  have h0 : gc = 0 := by linear_combination h / 2
  rw [h0, norm_zero] at hc
  exact zero_ne_one hc

/-! ### Translation invariance of the Markov pairing -/

theorem markovPair_comp_sub (f d : ℝ → ℝ) (c : ℝ) :
    markovPair (fun u => f (u - c)) (fun u => d (u - c)) = markovPair f d := by
  have hshift : ∀ φ : ℝ → ℝ, ∫ u, φ (u - c) = ∫ u, φ u := fun φ =>
    integral_sub_right_eq_self (μ := (volume : Measure ℝ)) φ c
  have h1 : ∫ u, f (u - c) * d (u - c) = ∫ u, f u * d u := hshift fun u => f u * d u
  have h2 : ∫ y in Ioi 0, levyMixed (fun u => f (u - c)) (fun u => d (u - c)) y =
      ∫ y in Ioi 0, levyMixed f d y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    unfold levyMixed
    congr 1
    rw [← hshift fun u => (f u - f (u + y)) * (d u - d (u + y))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
      simp only [sub_add_eq_add_sub])
  have h3 : primePair (fun u => f (u - c)) (fun u => d (u - c)) = primePair f d := by
    unfold primePair
    apply tsum_congr
    intro k
    have e1 : ∫ t, f (t - c) * d (t - Real.log k - c) = ∫ t, f t * d (t - Real.log k) := by
      rw [← hshift fun t => f t * d (t - Real.log k)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
        simp only [sub_right_comm])
    have e2 : ∫ t, f (t - c) * d (t + Real.log k - c) = ∫ t, f t * d (t + Real.log k) := by
      rw [← hshift fun t => f t * d (t + Real.log k)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
        simp only [sub_add_eq_add_sub])
    beta_reduce
    rw [e1, e2]
  unfold markovPair
  rw [h1, h2, h3]

/-! ### Narrow windows see no prime lag -/

/-- A test supported in `[0, ℓ]` with `ℓ < log 2` has no prime sum. -/
theorem primeSum_eq_zero_of_narrow {h : ℝ → ℝ} {ℓ : ℝ} (hℓ : ℓ < Real.log 2)
    (hsupp : ∀ u, u ∉ Set.Icc 0 ℓ → h u = 0) : primeSum h = 0 := by
  unfold primeSum
  refine (tsum_congr fun k => ?_).trans tsum_zero
  by_cases hk : 2 ≤ k
  · have hlog : Real.log 2 ≤ Real.log k :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hk)
    have hz : ∀ c : ℝ, ℓ < |c| → ∀ t, h t * h (t + c) = 0 := fun c hc t => by
      by_cases ht : t ∈ Set.Icc 0 ℓ
      · have : t + c ∉ Set.Icc 0 ℓ := fun h' => by
          have : |c| ≤ ℓ := by
            rw [abs_le]; constructor <;> linarith [ht.1, ht.2, h'.1, h'.2]
          linarith
        rw [hsupp _ this, mul_zero]
      · rw [hsupp t ht, zero_mul]
    have hpos : 0 ≤ Real.log k := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hc1 : ℓ < |Real.log k| := by rw [abs_of_nonneg hpos]; linarith
    have hc2 : ℓ < |-Real.log k| := by rw [abs_neg]; exact hc1
    have h1 : ∫ t, h t * h (t - Real.log k) = 0 := by
      simp_rw [sub_eq_add_neg]; simp [hz _ hc2]
    have h2 : ∫ t, h t * h (t + Real.log k) = 0 := by simp [hz _ hc1]
    rw [h1, h2]; simp
  · simp [vonMangoldtAtom, hk]

/-! ### Polarization -/

/-- **Polarization**: `M(a + b) − M(a − b) = 4 M(a, b)`. -/
theorem levyMarkovForm_add_sub_sub {R : ℝ} {a b : ℝ → ℝ} (ha : ContDiff ℝ 2 a)
    (hac : HasCompactSupport a) (haR : SupportedIn R a) (hb : ContDiff ℝ 2 b)
    (hbc : HasCompactSupport b) (hbR : SupportedIn R b) :
    levyMarkovForm (fun u => a u + b u) - levyMarkovForm (fun u => a u - b u) =
      4 * markovPair a b := by
  set e : Fin 2 → ℝ → ℝ := ![a, b]
  have he : ∀ i, ContDiff ℝ 2 (e i) := fun i => by fin_cases i <;> simpa [e]
  have hec : ∀ i, HasCompactSupport (e i) := fun i => by fin_cases i <;> simpa [e]
  have heR : ∀ i, SupportedIn R (e i) := fun i => by fin_cases i <;> simpa [e]
  have h1 := levyMarkovForm_sum_eq univ he hec heR ![1, 1]
  have h2 := levyMarkovForm_sum_eq univ he hec heR ![1, -1]
  simp only [Fin.sum_univ_two, e, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_mul, mul_one, mul_neg, neg_neg] at h1 h2
  rw [show (fun u => a u + b u) = fun u => a u + b u from rfl, h1,
    show (fun u => a u - b u) = fun u => a u + -1 * b u by funext u; ring, h2, markovPair_comm b a]
  ring

/-! ### Elementary integral bounds -/

/-- A function bounded by `M` and vanishing off `[0, ℓ]` has `∫ |φ| ≤ Mℓ` and `∫ φ² ≤ M²ℓ`. -/
theorem integral_abs_le_and_sq_le {φ : ℝ → ℝ} (hφ : Continuous φ) {M ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hM : ∀ u, |φ u| ≤ M) (hsupp : ∀ u, u ∉ Set.Icc 0 ℓ → φ u = 0) :
    (∫ u, |φ u|) ≤ M * ℓ ∧ (∫ u, φ u ^ 2) ≤ M ^ 2 * ℓ := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hvol : (volume (Set.Icc (0 : ℝ) ℓ)).toReal = ℓ := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
  have key : ∀ ψ : ℝ → ℝ, Continuous ψ → (∀ u, u ∉ Set.Icc 0 ℓ → ψ u = 0) →
      ∀ C : ℝ, (∀ u, ψ u ≤ C) → (∫ u, ψ u) ≤ C * ℓ := fun ψ hψ hψs C hC => by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc 0 ℓ) hψs]
    calc (∫ u in Set.Icc 0 ℓ, ψ u) ≤ ∫ u in Set.Icc 0 ℓ, C :=
          setIntegral_mono_on (hψ.integrableOn_Icc) (integrableOn_const (by simp))
            measurableSet_Icc fun u _ => hC u
      _ = C * ℓ := by rw [setIntegral_const, smul_eq_mul, mul_comm, Measure.real, hvol]
  refine ⟨key (fun u => |φ u|) hφ.abs (fun u hu => by simp only [hsupp u hu, abs_zero]) M hM,
    key (fun u => φ u ^ 2) (hφ.pow 2) (fun u hu => by simp only [hsupp u hu]; ring) (M ^ 2)
      fun u => ?_⟩
  show φ u ^ 2 ≤ M ^ 2
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hM u) 2

theorem levyLipConstant_pos : 0 < levyLipConstant := by
  unfold levyLipConstant
  have : 0 < 1 - Real.exp (-2) := by
    have := Real.exp_lt_one_iff.mpr (by norm_num : (-2 : ℝ) < 0); linarith
  positivity

/-! ### Close atoms meet positively -/

variable {g : ℝ → ℝ} {w : ℝ}

/-- **Close atoms meet positively.** For a nonnegative `K`-Lipschitz `C²` bump supported in `[0, w]`
with `2w < log 2` and `κ = 2θ′(0) + log(1/(2w)) > 0`, the Markov pairing of `g` with its translate by
`0 < s ≤ w` is positive as soon as the Lévy cost of `g − g(· − s)` is below `κ‖g‖²`. -/
theorem markovPair_shift_pos (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hg0 : ∀ u, 0 ≤ g u) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ u v, |g u - g v| ≤ K * |u - v|) (hw0 : 0 < w) (hw2 : 2 * w < Real.log 2)
    (hκ : 0 < 2 * gammaHardyPhaseRate 0 + Real.log (1 / (2 * w))) {s : ℝ} (hs0 : 0 < s)
    (hsw : s ≤ w)
    (hsmall : 4 * Real.exp (1 / 2) * K ^ 2 * w ^ 2 * s +
        2 * w * K ^ 2 * (2 * Real.log (1 / w) + levyLipConstant + 2 * |gammaHardyPhaseRate 0|) *
          s ^ 2 <
      (2 * gammaHardyPhaseRate 0 + Real.log (1 / (2 * w))) * ∫ u, g u ^ 2) :
    0 < markovPair g (fun u => g (u - s)) := by
  set θ := gammaHardyPhaseRate 0
  set b : ℝ → ℝ := fun u => g (u - s)
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hw1 : w ≤ 1 := by linarith
  have hb : ContDiff ℝ 2 b := hg.comp (contDiff_id.sub contDiff_const)
  have hbc : HasCompactSupport b := hgc.comp_homeomorph (Homeomorph.subRight s)
  -- `g`, its translate, their sum and difference vanish off `[0, 2w]`
  have hsupp2 : ∀ u, u ∉ Set.Icc 0 (2 * w) → g u = 0 ∧ b u = 0 := fun u hu => by
    refine ⟨hgsupp u fun h => hu ⟨h.1, by linarith [h.2]⟩, hgsupp _ fun h => hu ⟨?_, ?_⟩⟩
    · linarith [h.1]
    · linarith [h.2]
  have hR : ∀ φ : ℝ → ℝ, (∀ u, u ∉ Set.Icc 0 (2 * w) → φ u = 0) → SupportedIn (2 * w + 1) φ :=
    fun φ hφ u hu => hφ u fun h => by
      have : |u| ≤ 2 * w := abs_le.mpr ⟨by linarith [h.1], h.2⟩
      linarith
  have habs : ∀ u, u ∉ Set.Icc 0 (2 * w) → g u + b u = 0 := fun u hu => by
    rw [(hsupp2 u hu).1, (hsupp2 u hu).2, add_zero]
  have hds : ∀ u, u ∉ Set.Icc 0 (2 * w) → g u - b u = 0 := fun u hu => by
    rw [(hsupp2 u hu).1, (hsupp2 u hu).2, sub_zero]
  have hab : ContDiff ℝ 2 fun u => g u + b u := hg.add hb
  have habc : HasCompactSupport fun u => g u + b u := hgc.add hbc
  have hd : ContDiff ℝ 2 fun u => g u - b u := hg.sub hb
  have hdc : HasCompactSupport fun u => g u - b u := hgc.sub hbc
  -- the sum is a bump of width `2w`: self-energy `≥ κ ‖g‖²`
  have hLab : (2 * θ + Real.log (1 / (2 * w))) * ∫ u, g u ^ 2 ≤
      levyMarkovForm fun u => g u + b u := by
    have h1 := archForm_atom_ge hab habc habs (by linarith) (by linarith)
    have h2 : primeSum (fun u => g u + b u) = 0 := primeSum_eq_zero_of_narrow hw2 habs
    have h3 : levyMarkovForm (fun u => g u + b u) =
        archForm (fun u => g u + b u) - primeSum (fun u => g u + b u) := by
      rw [levyMarkovForm, archForm_eq_levyEnergy hab habc]
    have h4 : ∫ u, g u ^ 2 ≤ ∫ u, (g u + b u) ^ 2 :=
      integral_mono (integrable_sq_of_continuous hg.continuous hgc)
        (integrable_sq_of_continuous hab.continuous habc) fun u => by
          have := hg0 u; have := hg0 (u - s); simp only [b]; nlinarith
    rw [h3, h2, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_left h4 hκ.le]
  -- the difference is small in the Lévy norm
  have hLd : levyMarkovForm (fun u => g u - b u) ≤
      4 * Real.exp (1 / 2) * K ^ 2 * w ^ 2 * s +
        2 * w * K ^ 2 * (2 * Real.log (1 / w) + levyLipConstant + 2 * |θ|) * s ^ 2 := by
    have hdK : ∀ u v, |(g u - b u) - (g v - b v)| ≤ 2 * K * |u - v| := fun u v => by
      have h1 := hK u v
      have h2 := hK (u - s) (v - s)
      rw [show u - s - (v - s) = u - v by ring] at h2
      calc |(g u - b u) - (g v - b v)| = |(g u - g v) - (g (u - s) - g (v - s))| := by
            simp only [b]; ring_nf
        _ ≤ |g u - g v| + |g (u - s) - g (v - s)| := abs_sub _ _
        _ ≤ 2 * K * |u - v| := by linarith
    have hdM : ∀ u, |g u - b u| ≤ K * s := fun u => by
      have := hK u (u - s)
      rwa [show u - (u - s) = s by ring, abs_of_pos hs0] at this
    obtain ⟨hd1, hd2⟩ := integral_abs_le_and_sq_le hd.continuous (by linarith) hdM hds
    have hlev := levyEnergy_le_lipschitz hd hdc hdK hw0 hw1
    have hprime : primeSum (fun u => g u - b u) = 0 := primeSum_eq_zero_of_narrow hw2 hds
    have hlog : 0 ≤ 2 * Real.log (1 / w) + levyLipConstant := by
      have := Real.log_nonneg (one_le_one_div hw0 hw1); linarith [levyLipConstant_pos]
    have hI : 0 ≤ ∫ u, (g u - b u) ^ 2 := integral_nonneg fun u => sq_nonneg _
    have e1 : Real.exp (1 / 2) * (2 * K) * w * (∫ u, |g u - b u|) ≤
        Real.exp (1 / 2) * (2 * K) * w * (K * s * (2 * w)) :=
      mul_le_mul_of_nonneg_left hd1 (by positivity)
    have e2 : (2 * Real.log (1 / w) + levyLipConstant) * (∫ u, (g u - b u) ^ 2) ≤
        (2 * Real.log (1 / w) + levyLipConstant) * ((K * s) ^ 2 * (2 * w)) :=
      mul_le_mul_of_nonneg_left hd2 hlog
    have e3 : 2 * θ * (∫ u, (g u - b u) ^ 2) ≤ 2 * |θ| * ((K * s) ^ 2 * (2 * w)) :=
      (mul_le_mul_of_nonneg_right (by linarith [le_abs_self θ]) hI).trans
        (mul_le_mul_of_nonneg_left hd2 (by positivity))
    have hsum : Real.exp (1 / 2) * (2 * K) * w * (K * s * (2 * w)) +
        (2 * Real.log (1 / w) + levyLipConstant) * ((K * s) ^ 2 * (2 * w)) +
          2 * |θ| * ((K * s) ^ 2 * (2 * w)) =
        4 * Real.exp (1 / 2) * K ^ 2 * w ^ 2 * s +
          2 * w * K ^ 2 * (2 * Real.log (1 / w) + levyLipConstant + 2 * |θ|) * s ^ 2 := by ring
    unfold levyMarkovForm
    rw [hprime, sub_zero]
    linarith
  have hpol := levyMarkovForm_add_sub_sub hg hgc (hR g fun u hu => (hsupp2 u hu).1) hb hbc
    (hR b fun u hu => (hsupp2 u hu).2)
  linarith

/-- **Close atoms meet positively**: the Markov pairing of the atoms `m < n` is the pairing of `g`
with its translate by `log n − log m`. -/
theorem markovPair_atom_eq_shift (g : ℝ → ℝ) (m n : ℕ) :
    markovPair (atom g m) (atom g n) =
      markovPair g (fun u => g (u - (Real.log n - Real.log m))) := by
  have := markovPair_comp_sub g (fun u => g (u - (Real.log n - Real.log m))) (Real.log m)
  rw [← this]
  congr 1
  funext u; simp only [atom]; ring_nf

/-! ### At fixed width the atomic form is frustrated -/

/-- **A positive triangle of atoms frustrates every gauge.** If the atoms `N − 2, N − 1, N` meet
pairwise positively, no unimodular gauge makes the atom block `−M` entrywise nonnegative. -/
theorem not_nonneg_gauge_of_pos_triangle_atoms (g : ℝ → ℝ) {N : ℕ} (hN : 3 ≤ N)
    (h1 : 0 < markovPair (atom g (N - 2)) (atom g (N - 1)))
    (h2 : 0 < markovPair (atom g (N - 1)) (atom g N))
    (h3 : 0 < markovPair (atom g (N - 2)) (atom g N)) :
    ¬ ∃ γ : Fin N → ℂ, (∀ i, ‖γ i‖ = 1) ∧
      ∀ i j, i ≠ j → 0 ≤ conj (γ i) * γ j * ((-atomicMarkovGram g N i j : ℝ) : ℂ) := by
  rintro ⟨γ, hγ, hnn⟩
  set i : Fin N := ⟨N - 3, by omega⟩
  set j : Fin N := ⟨N - 2, by omega⟩
  set k : Fin N := ⟨N - 1, by omega⟩
  have hij : i ≠ j := fun h => by simp [i, j, Fin.ext_iff] at h; omega
  have hjk : j ≠ k := fun h => by simp [j, k, Fin.ext_iff] at h; omega
  have hik : i ≠ k := fun h => by simp [i, k, Fin.ext_iff] at h; omega
  have e : ∀ (x y : Fin N), atomicMarkovGram g N x y =
      markovPair (atom g ((x : ℕ) + 1)) (atom g ((y : ℕ) + 1)) := fun _ _ => rfl
  have ei : (i : ℕ) + 1 = N - 2 := by simp [i]; omega
  have ej : (j : ℕ) + 1 = N - 1 := by simp [j]; omega
  have ek : (k : ℕ) + 1 = N := by simp [k]; omega
  refine not_nonneg_gauge_of_neg_triangle (Kab := -atomicMarkovGram g N i j)
    (Kbc := -atomicMarkovGram g N j k) (Kac := -atomicMarkovGram g N i k) ?_ ?_ ?_
    (hγ i) (hγ j) (hγ k) ⟨hnn i j hij, hnn j k hjk, hnn i k hik⟩
  · rw [e, ei, ej]; linarith
  · rw [e, ej, ek]; linarith
  · rw [e, ei, ek]; linarith

/-- **No Metzler gauge beyond the spacing.** If the atoms `N − 2, N − 1, N` lie within the window
where close atoms meet positively, no unimodular gauge makes the atom block `−M` of the atomic
intersection form entrywise nonnegative. -/
theorem atomicMarkovGram_frustrated (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hg0 : ∀ u, 0 ≤ g u) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ u v, |g u - g v| ≤ K * |u - v|) (hw0 : 0 < w) (hw2 : 2 * w < Real.log 2)
    (hκ : 0 < 2 * gammaHardyPhaseRate 0 + Real.log (1 / (2 * w))) {N : ℕ} (hN : 3 ≤ N)
    (hgap : Real.log N - Real.log (N - 2 : ℕ) ≤ w)
    (hsmall : 4 * Real.exp (1 / 2) * K ^ 2 * w ^ 2 * (Real.log N - Real.log (N - 2 : ℕ)) +
        2 * w * K ^ 2 * (2 * Real.log (1 / w) + levyLipConstant + 2 * |gammaHardyPhaseRate 0|) *
          (Real.log N - Real.log (N - 2 : ℕ)) ^ 2 <
      (2 * gammaHardyPhaseRate 0 + Real.log (1 / (2 * w))) * ∫ u, g u ^ 2) :
    ¬ ∃ γ : Fin N → ℂ, (∀ i, ‖γ i‖ = 1) ∧
      ∀ i j, i ≠ j → 0 ≤ conj (γ i) * γ j * ((-atomicMarkovGram g N i j : ℝ) : ℂ) := by
  rintro ⟨γ, hγ, hnn⟩
  -- the three atoms `N − 2 < N − 1 < N`
  set S := Real.log N - Real.log (N - 2 : ℕ)
  have hlog : ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ N → N - 2 ≤ a →
      0 < Real.log b - Real.log a ∧ Real.log b - Real.log a ≤ S := fun a b ha hab hbN hNa => by
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hab' : (a : ℝ) < b := by exact_mod_cast hab
    refine ⟨sub_pos.mpr (Real.log_lt_log ha' hab'), ?_⟩
    have h1 : Real.log b ≤ Real.log N := Real.log_le_log (by linarith) (by exact_mod_cast hbN)
    have h2 : Real.log (N - 2 : ℕ) ≤ Real.log a :=
      Real.log_le_log (by exact_mod_cast (show 0 < N - 2 by omega)) (by exact_mod_cast hNa)
    linarith
  have hpos : ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ N → N - 2 ≤ a →
      0 < markovPair (atom g a) (atom g b) := fun a b ha hab hbN hNa => by
    obtain ⟨h0, hS⟩ := hlog a b ha hab hbN hNa
    rw [markovPair_atom_eq_shift]
    refine markovPair_shift_pos hg hgc hg0 hgsupp hK0 hK hw0 hw2 hκ h0 (hS.trans hgap)
      (lt_of_le_of_lt ?_ hsmall)
    have hS0 : 0 ≤ Real.log b - Real.log a := h0.le
    have hc : 0 ≤ 2 * w * K ^ 2 * (2 * Real.log (1 / w) + levyLipConstant +
        2 * |gammaHardyPhaseRate 0|) := by
      have := Real.log_nonneg (one_le_one_div hw0 (by linarith [Real.log_two_lt_d9]))
      have := levyLipConstant_pos
      positivity
    have : (Real.log b - Real.log a) ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hS0 hS 2
    nlinarith [mul_le_mul_of_nonneg_left hS (by positivity :
      (0 : ℝ) ≤ 4 * Real.exp (1 / 2) * K ^ 2 * w ^ 2)]
  exact not_nonneg_gauge_of_pos_triangle_atoms g hN
    (hpos (N - 2) (N - 1) (by omega) (by omega) (by omega) le_rfl)
    (hpos (N - 1) N (by omega) (by omega) le_rfl (by omega))
    (hpos (N - 2) N (by omega) (by omega) le_rfl le_rfl) ⟨γ, hγ, hnn⟩

/-- A quadratic `At + Bt²` stays below `C > 0` on a whole interval `[0, s]` with `0 < s ≤ w`. -/
theorem exists_pos_quadratic_lt {A B C w : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 < C) (hw : 0 < w) :
    ∃ s, 0 < s ∧ s ≤ w ∧ ∀ t, 0 ≤ t → t ≤ s → A * t + B * t ^ 2 < C := by
  refine ⟨min w (min 1 (C / (2 * (A + B + 1)))), lt_min hw (lt_min one_pos (by positivity)),
    min_le_left _ _, fun t ht0 hts => ?_⟩
  have hs1 : t ≤ 1 := hts.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsC : t ≤ C / (2 * (A + B + 1)) := hts.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h1 : A * t + B * t ^ 2 ≤ (A + B) * t := by nlinarith [mul_le_mul_of_nonneg_left hs1 hB]
  have h2 : (A + B) * t ≤ (A + B) * (C / (2 * (A + B + 1))) :=
    mul_le_mul_of_nonneg_left hsC (by linarith)
  have h3 : (A + B) * (C / (2 * (A + B + 1))) < C := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  linarith

/-- `log N − log(N − 2) ≤ s` once `N ≥ ⌈2/s⌉ + 3`. -/
theorem log_sub_log_two_le {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : ⌈2 / s⌉₊ + 3 ≤ N) :
    0 ≤ Real.log N - Real.log (N - 2 : ℕ) ∧ Real.log N - Real.log (N - 2 : ℕ) ≤ s := by
  have hN2 : (0 : ℝ) < (N - 2 : ℕ) := by exact_mod_cast (show 0 < N - 2 by omega)
  have hcast : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨sub_nonneg.mpr (Real.log_le_log hN2 (by exact_mod_cast (show N - 2 ≤ N by omega))), ?_⟩
  rw [← Real.log_div hNpos.ne' hN2.ne']
  have hle := Real.log_le_sub_one_of_pos (div_pos hNpos hN2)
  have hceil : 2 / s + 1 ≤ ((N - 2 : ℕ) : ℝ) := by
    have h1 := Nat.le_ceil (2 / s)
    have h2 : (⌈2 / s⌉₊ : ℝ) + 1 ≤ ((N - 2 : ℕ) : ℝ) := by
      exact_mod_cast (show ⌈2 / s⌉₊ + 1 ≤ N - 2 by omega)
    linarith
  have hfrac : (N : ℝ) / (N - 2 : ℕ) - 1 = 2 / (N - 2 : ℕ) := by
    rw [hcast] at hN2 ⊢; field_simp; ring
  have h2 : 2 / ((N - 2 : ℕ) : ℝ) ≤ s := by
    rw [div_le_iff₀ hN2]
    have := mul_le_mul_of_nonneg_left hceil hs.le
    rw [mul_add, mul_div_cancel₀ _ hs.ne'] at this
    linarith
  linarith

/-- **At fixed width the atomic form is frustrated for every large `N`.** For a nonzero
nonnegative Lipschitz `C²` bump with `2w < log 2` and `κ > 0`, there is `N₀` such that for every
`N ≥ N₀` no unimodular gauge makes the atom block `−M` of the atomic intersection form nonnegative. -/
theorem atomicMarkovGram_frustrated_eventually (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hg0 : ∀ u, 0 ≤ g u) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {u₀ : ℝ} (hu₀ : 0 < g u₀)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ u v, |g u - g v| ≤ K * |u - v|) (hw0 : 0 < w)
    (hw2 : 2 * w < Real.log 2) (hκ : 0 < 2 * gammaHardyPhaseRate 0 + Real.log (1 / (2 * w))) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ¬ ∃ γ : Fin N → ℂ, (∀ i, ‖γ i‖ = 1) ∧
      ∀ i j, i ≠ j → 0 ≤ conj (γ i) * γ j * ((-atomicMarkovGram g N i j : ℝ) : ℂ) := by
  have hw1 : w ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hB : 0 ≤ 2 * w * K ^ 2 *
      (2 * Real.log (1 / w) + levyLipConstant + 2 * |gammaHardyPhaseRate 0|) := by
    have := Real.log_nonneg (one_le_one_div hw0 hw1); have := levyLipConstant_pos; positivity
  have hgc2 : HasCompactSupport fun u => g u ^ 2 := by
    rw [show (fun u => g u ^ 2) = g * g from funext fun u => by simp [sq]]
    exact hgc.mul_right
  have hg2 : 0 < ∫ u, g u ^ 2 :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := u₀) (hg.continuous.pow 2)
      hgc2 (fun u => sq_nonneg _) (pow_ne_zero 2 hu₀.ne')
  obtain ⟨s, hs0, hsw, hcrit⟩ := exists_pos_quadratic_lt
    (by positivity : (0 : ℝ) ≤ 4 * Real.exp (1 / 2) * K ^ 2 * w ^ 2) hB (mul_pos hκ hg2) hw0
  refine ⟨⌈2 / s⌉₊ + 3, fun N hN => ?_⟩
  obtain ⟨hS0, hS⟩ := log_sub_log_two_le hs0 hN
  exact atomicMarkovGram_frustrated hg hgc hg0 hgsupp hK0 hK hw0 hw2 hκ (by omega) (hS.trans hsw)
    (hcrit _ hS0 hS)

end GaloisForLFunctions.ArithmeticLorentzianGeometry
