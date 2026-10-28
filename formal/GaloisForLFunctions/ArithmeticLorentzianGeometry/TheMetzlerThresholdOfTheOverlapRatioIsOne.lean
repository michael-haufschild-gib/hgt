import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheOverlapFrustratesTheMetzlerGauge
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomIsExactlyLogarithmic

/-!
# The Metzler threshold of the overlap ratio is one

Atoms `g(· − log n)`, `n ≤ N`, of a bump of width `w = ρ δ_N` have **overlap ratio** `ρ`. Below the
spacing (`ρ < 1`) the Euler-gauge atomic intersection form is Metzler
(`TheAtomicFormIsMetzlerBelowTheSpacing`). This file shows that `ρ = 1` is sharp: for the dilated
bump `g₁(·/w)` of a profile positive on `(0, 1)`, every `ρ > 1` frustrates every unimodular gauge
once `N` is large.

* **The overlap law** (`markovPair_shift_ge`): for a nonnegative `K`-Lipschitz `C²` bump in
  `[0, w]`, `2w < log 2`, and `0 ≤ s ≤ w`,

      M(g, g(· − s)) ≥ (2θ′(0) + log(1/(2w))) ⟨g, g(· − s)⟩ − 2e^{1/2} K w ‖g‖₁.

  Beyond the joint support `[0, 2w]` the shifted copies no longer meet, so the mixed Lévy integrand
  is `2ω(y)⟨g, g(· − s)⟩`, and `ω(y) ≥ 1/(2y)` integrates to `log(1/(2w))`; below it the Lipschitz
  bound costs `e^{1/2}K‖g‖₁` per unit shift; no prime lag fits in `[0, 2w]`. So overlapping atoms
  meet with their overlap times the self-energy, which is positive for `w` small.
* **Separated atoms meet strictly negatively** (`markovPair_atom_neg`): the Lévy kernel sees the
  translate overlap `∫ g_m g_n(· + y) ≈ ‖g‖²` for `y` near `log(n/m)`.
* **An odd triangle is frustrated** (`not_nonneg_gauge_of_odd_triangle`): one negative and two
  positive entries admit no unimodular gauge making all three nonnegative.
* **The threshold** (`metzlerThreshold_overlapRatio`): for a profile `g₁` positive on `(0, 1)`,
  the atomic intersection form of `g₁(·/(ρδ_N))` is Metzler for `ρ < 1`, and for `ρ > 1` the atoms
  `N − 1, N` (overlapping, positive pairing) and `1` (separated, negative pairings) form an odd
  triangle for all large `N`, so no unimodular gauge makes it Metzler.

So the Metzler property of `ζ`'s atomic intersection form holds exactly up to atomic resolution.
A trickle-down proof at any overlap ratio `ρ > 1` must leave diagonal gauges of the atomic basis.
-/

noncomputable section

open MeasureTheory Set Finset Matrix RHTower Complex
open scoped Real ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

/-! ### An odd triangle is frustrated -/

/-- **An odd triangle is frustrated.** Entries `K_ab < 0 < K_bc, K_ac` admit no unimodular gauge
making all three `conj γ_i γ_j K_ij` nonnegative: it would force `γ_a = −γ_b`, `γ_b = γ_c = γ_a`. -/
theorem not_nonneg_gauge_of_odd_triangle {Kab Kbc Kac : ℝ} (hab : Kab < 0) (hbc : 0 < Kbc)
    (hac : 0 < Kac) {ga gb gc : ℂ} (ha : ‖ga‖ = 1) (hb : ‖gb‖ = 1) (hc : ‖gc‖ = 1) :
    ¬ (0 ≤ conj ga * gb * (Kab : ℂ) ∧ 0 ≤ conj gb * gc * (Kbc : ℂ) ∧
      0 ≤ conj ga * gc * (Kac : ℂ)) := by
  rintro ⟨h1, h2, h3⟩
  have e : conj ga * gb * (Kab : ℂ) = conj ga * (-gb) * ((-Kab : ℝ) : ℂ) := by push_cast; ring
  rw [e] at h1
  have e1 := eq_of_conj_mul_nonneg ha (by rw [norm_neg, hb]) (by linarith) h1
  have e2 := eq_of_conj_mul_nonneg hb hc hbc h2
  have e3 := eq_of_conj_mul_nonneg ha hc hac h3
  have h : gb = -gb := by rw [← e1]; exact e2.trans e3.symm
  have h0 : gb = 0 := by linear_combination h / 2
  rw [h0, norm_zero] at hb
  exact zero_ne_one hb

/-- **An odd triangle of atoms frustrates every gauge.** If the atoms `N − 1, N` meet positively
and both meet the atom `1` negatively, no unimodular gauge makes the atom block `−M` of the atomic
intersection form entrywise nonnegative. -/
theorem not_nonneg_gauge_of_odd_triangle_atoms (g : ℝ → ℝ) {N : ℕ} (hN : 3 ≤ N)
    (h1 : 0 < markovPair (atom g (N - 1)) (atom g N))
    (h2 : markovPair (atom g 1) (atom g N) < 0)
    (h3 : markovPair (atom g 1) (atom g (N - 1)) < 0) :
    ¬ ∃ γ : Fin N → ℂ, (∀ i, ‖γ i‖ = 1) ∧
      ∀ i j, i ≠ j → 0 ≤ conj (γ i) * γ j * ((-atomicMarkovGram g N i j : ℝ) : ℂ) := by
  rintro ⟨γ, hγ, hnn⟩
  set i : Fin N := ⟨N - 2, by omega⟩
  set j : Fin N := ⟨N - 1, by omega⟩
  set k : Fin N := ⟨0, by omega⟩
  have hij : i ≠ j := fun h => by simp [i, j, Fin.ext_iff] at h; omega
  have hjk : j ≠ k := fun h => by simp [j, k, Fin.ext_iff] at h; omega
  have hik : i ≠ k := fun h => by simp [i, k, Fin.ext_iff] at h; omega
  have e : ∀ (x y : Fin N), atomicMarkovGram g N x y =
      markovPair (atom g ((x : ℕ) + 1)) (atom g ((y : ℕ) + 1)) := fun _ _ => rfl
  have ei : (i : ℕ) + 1 = N - 1 := by simp [i]; omega
  have ej : (j : ℕ) + 1 = N := by simp [j]; omega
  have ek : (k : ℕ) + 1 = 1 := by simp [k]
  refine not_nonneg_gauge_of_odd_triangle (Kab := -atomicMarkovGram g N i j)
    (Kbc := -atomicMarkovGram g N j k) (Kac := -atomicMarkovGram g N i k) ?_ ?_ ?_
    (hγ i) (hγ j) (hγ k) ⟨hnn i j hij, hnn j k hjk, hnn i k hik⟩
  · rw [e, ei, ej]; linarith
  · rw [e, ej, ek, markovPair_comm]; linarith
  · rw [e, ei, ek, markovPair_comm]; linarith

/-! ### The overlap law -/

/-- Tests vanishing off `[0, ℓ]`, `ℓ < log 2`, have no prime pairing. -/
theorem primePair_eq_zero_of_narrow {a b : ℝ → ℝ} {ℓ : ℝ} (hℓ : ℓ < Real.log 2)
    (ha : ∀ u, u ∉ Set.Icc 0 ℓ → a u = 0) (hb : ∀ u, u ∉ Set.Icc 0 ℓ → b u = 0) :
    primePair a b = 0 := by
  unfold primePair
  refine (tsum_congr fun k => ?_).trans tsum_zero
  by_cases hk : 2 ≤ k
  · have hlog : Real.log 2 ≤ Real.log k :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hk)
    have hz : ∀ c : ℝ, ℓ < |c| → ∀ t, a t * b (t + c) = 0 := fun c hc t => by
      by_cases ht : t ∈ Set.Icc 0 ℓ
      · have : t + c ∉ Set.Icc 0 ℓ := fun h' => by
          have : |c| ≤ ℓ := by
            rw [abs_le]; constructor <;> linarith [ht.1, ht.2, h'.1, h'.2]
          linarith
        rw [hb _ this, mul_zero]
      · rw [ha t ht, zero_mul]
    have hpos : 0 ≤ Real.log k := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hc1 : ℓ < |Real.log k| := by rw [abs_of_nonneg hpos]; linarith
    have hc2 : ℓ < |-Real.log k| := by rw [abs_neg]; exact hc1
    have h1 : ∫ t, a t * b (t - Real.log k) = 0 := by
      simp_rw [sub_eq_add_neg]; simp [hz _ hc2]
    have h2 : ∫ t, a t * b (t + Real.log k) = 0 := by simp [hz _ hc1]
    rw [h1, h2]; simp
  · simp [vonMangoldtAtom, hk]

/-- Beyond the joint support `[0, ℓ]` the shifted copies no longer meet:
`levyMixed a b y = 2⟨a, b⟩ ω(y)` for `y > ℓ`. -/
theorem levyMixed_eq_of_far {a b : ℝ → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) {ℓ : ℝ} (ha0 : ∀ u, u ∉ Set.Icc 0 ℓ → a u = 0)
    (hb0 : ∀ u, u ∉ Set.Icc 0 ℓ → b u = 0) {y : ℝ} (hy : ℓ < y) :
    levyMixed a b y = 2 * (∫ u, a u * b u) * archLevyDensity y := by
  have hz : ∀ f d : ℝ → ℝ, (∀ u, u ∉ Set.Icc 0 ℓ → f u = 0) →
      (∀ u, u ∉ Set.Icc 0 ℓ → d u = 0) → ∀ u, f u * d (u + y) = 0 := fun f d hf hd u => by
    by_cases hu : u ∈ Set.Icc 0 ℓ
    · rw [hd (u + y) fun h => by linarith [hu.1, h.2], mul_zero]
    · rw [hf u hu, zero_mul]
  have e : ∀ u, (a u - a (u + y)) * (b u - b (u + y)) = a u * b u + a (u + y) * b (u + y) :=
    fun u => by linear_combination (-1 : ℝ) * hz a b ha0 hb0 u - hz b a hb0 ha0 u
  have hi : Integrable fun u => a u * b u := by
    simpa using integrable_mul_shift ha hac hb 0
  unfold levyMixed
  simp_rw [e]
  rw [integral_add hi (hi.comp_add_right y), integral_add_right_eq_self (fun u => a u * b u) y]
  ring

/-- **Near shifts cost little**: for `K`-Lipschitz tests and `0 < y ≤ 1`,
`levyMixed a b y ≥ −e^{1/2} K (‖a‖₁ + ‖b‖₁)/2`. -/
theorem levyMixed_ge_lipschitz {a b : ℝ → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) {K : ℝ} (hK0 : 0 ≤ K)
    (hKa : ∀ u v, |a u - a v| ≤ K * |u - v|) (hKb : ∀ u v, |b u - b v| ≤ K * |u - v|)
    {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    -(Real.exp (1 / 2) * K * ((∫ u, |a u|) + ∫ u, |b u|) / 2) ≤ levyMixed a b y := by
  set A := (∫ u, |a u|) + ∫ u, |b u|
  have hA : 0 ≤ A :=
    add_nonneg (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
  have h1 := integral_sub_shift_sq_le_lipschitz ha hac hKa y
  have h2 := integral_sub_shift_sq_le_lipschitz hb hbc hKb y
  rw [abs_of_pos hy0] at h1 h2
  -- `xz ≥ −(x² + z²)/2` under the integral
  have i1 := RHTower.WeilMarkovPole.integrable_sub_shift_sq ha hac y
  have i2 := RHTower.WeilMarkovPole.integrable_sub_shift_sq hb hbc y
  have hmix : -((∫ u, (a u - a (u + y)) ^ 2) + ∫ u, (b u - b (u + y)) ^ 2) / 2 ≤
      ∫ u, (a u - a (u + y)) * (b u - b (u + y)) := by
    have hval : ∫ u, -(((a u - a (u + y)) ^ 2 + (b u - b (u + y)) ^ 2) / 2) =
        -((∫ u, (a u - a (u + y)) ^ 2) + ∫ u, (b u - b (u + y)) ^ 2) / 2 := by
      rw [integral_neg, integral_div, integral_add i1 i2, neg_div]
    rw [← hval]
    exact integral_mono ((i1.add i2).div_const 2).neg (integrable_sub_shift_mul ha hac hb y)
      fun u => by nlinarith [sq_nonneg (a u - a (u + y) + (b u - b (u + y)))]
  have hI : -(K * y * A) ≤ ∫ u, (a u - a (u + y)) * (b u - b (u + y)) := by
    simp only [A]; linarith
  have hω0 := (archLevyDensity_pos hy0).le
  have hω := archLevyDensity_le_sqrt_e_div hy0 hy1
  unfold levyMixed
  calc -(Real.exp (1 / 2) * K * A / 2) = Real.exp (1 / 2) / (2 * y) * (-(K * y * A)) := by
        field_simp
    _ ≤ archLevyDensity y * (-(K * y * A)) :=
        mul_le_mul_of_nonpos_right hω (neg_nonpos.mpr (by positivity))
    _ ≤ archLevyDensity y * ∫ u, (a u - a (u + y)) * (b u - b (u + y)) :=
        mul_le_mul_of_nonneg_left hI hω0

variable {g : ℝ → ℝ} {w : ℝ}

/-- **The overlap law.** For a nonnegative `K`-Lipschitz `C²` bump supported in `[0, w]` with
`2w < log 2` and `0 ≤ s ≤ w`, the Markov pairing of `g` with its translate is at least its overlap
times the self-energy of the pair, less the Lipschitz cost of the near shifts:
`M(g, g(· − s)) ≥ (2θ′(0) + log(1/(2w))) ⟨g, g(· − s)⟩ − 2e^{1/2} K w ‖g‖₁`. -/
theorem markovPair_shift_ge (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hg0 : ∀ u, 0 ≤ g u) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ u v, |g u - g v| ≤ K * |u - v|) (hw0 : 0 < w) (hw2 : 2 * w < Real.log 2)
    {s : ℝ} (hs0 : 0 ≤ s) (hsw : s ≤ w) :
    (2 * gammaHardyPhaseRate 0 + Real.log (1 / (2 * w))) * (∫ u, g u * g (u - s)) -
      2 * Real.exp (1 / 2) * K * w * (∫ u, g u) ≤ markovPair g (fun u => g (u - s)) := by
  set θ := gammaHardyPhaseRate 0
  set b : ℝ → ℝ := fun u => g (u - s)
  set P := ∫ u, g u * b u
  set A := ∫ u, g u
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hb : ContDiff ℝ 2 b := hg.comp (contDiff_id.sub contDiff_const)
  have hbc : HasCompactSupport b := hgc.comp_homeomorph (Homeomorph.subRight s)
  have hP0 : 0 ≤ P := integral_nonneg fun u => mul_nonneg (hg0 u) (hg0 (u - s))
  -- `g` and its translate vanish off `[0, 2w]`
  have hg2 : ∀ u, u ∉ Set.Icc 0 (2 * w) → g u = 0 := fun u hu =>
    hgsupp u fun h => hu ⟨h.1, by linarith [h.2]⟩
  have hb2 : ∀ u, u ∉ Set.Icc 0 (2 * w) → b u = 0 := fun u hu =>
    hgsupp _ fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩
  have hKb : ∀ u v, |b u - b v| ≤ K * |u - v| := fun u v => by
    have := hK (u - s) (v - s); rwa [show u - s - (v - s) = u - v by ring] at this
  have hAb : ∫ u, |b u| = A := by
    rw [integral_sub_right_eq_self (fun u => |g u|) s]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => abs_of_nonneg (hg0 u))
  have hAg : ∫ u, |g u| = A :=
    integral_congr_ae (Filter.Eventually.of_forall fun u => abs_of_nonneg (hg0 u))
  -- split the Lévy integral at the joint support
  set F := levyMixed g b
  have hF : IntegrableOn F (Ioi 0) := integrableOn_levyMixed hg hgc hb hbc
  have hI1 : IntegrableOn F (Ioc 0 (2 * w)) := hF.mono_set Ioc_subset_Ioi_self
  have hI2 : IntegrableOn F (Ioi (2 * w)) := hF.mono_set (Ioi_subset_Ioi (by linarith))
  have hsplit : ∫ y in Ioi 0, F y = (∫ y in Ioc 0 (2 * w), F y) + ∫ y in Ioi (2 * w), F y := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hI2,
      Ioc_union_Ioi_eq_Ioi (by linarith)]
  -- near shifts
  have hnear : -(2 * Real.exp (1 / 2) * K * w * A) ≤ ∫ y in Ioc 0 (2 * w), F y := by
    have hb' : ∀ y ∈ Ioc 0 (2 * w), -(Real.exp (1 / 2) * K * A) ≤ F y := fun y hy => by
      have := levyMixed_ge_lipschitz hg.continuous hgc hb.continuous hbc hK0 hK hKb hy.1
        (by linarith [hy.2])
      rw [hAg, hAb] at this
      linarith
    have := setIntegral_mono_on (integrableOn_const measure_Ioc_lt_top.ne) hI1 measurableSet_Ioc hb'
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by linarith), sub_zero] at this
    linarith
  -- far shifts: `F = 2Pω ≥ 0`, and `2∫_{(2w, 1]} ω ≥ log(1/(2w))`
  have hfar_eq : ∀ y ∈ Ioi (2 * w), F y = 2 * P * archLevyDensity y := fun y hy =>
    levyMixed_eq_of_far hg.continuous hgc hb.continuous hg2 hb2 hy
  have hfar : P * Real.log (1 / (2 * w)) ≤ ∫ y in Ioi (2 * w), F y := by
    have hmono : ∫ y in Ioc (2 * w) 1, F y ≤ ∫ y in Ioi (2 * w), F y :=
      setIntegral_mono_set hI2
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => by
          rw [hfar_eq y hy]
          exact mul_nonneg (by positivity) (archLevyDensity_pos (by linarith [mem_Ioi.mp hy])).le))
        Ioc_subset_Ioi_self.eventuallyLE
    have hval : ∫ y in Ioc (2 * w) 1, F y = 2 * P * ∫ y in Ioc (2 * w) 1, archLevyDensity y := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioc fun y hy => hfar_eq y hy.1
    have hwin := log_div_le_two_mul_setIntegral_archLevyDensity (by linarith : (0 : ℝ) < 2 * w)
      (by linarith) le_rfl
    nlinarith [mul_le_mul_of_nonneg_left hwin hP0]
  have hprime : primePair g b = 0 := primePair_eq_zero_of_narrow hw2 hg2 hb2
  show (2 * θ + Real.log (1 / (2 * w))) * P - 2 * Real.exp (1 / 2) * K * w * A ≤
    2 * θ * P + (∫ y in Ioi 0, F y) - primePair g b
  rw [hsplit, hprime]
  nlinarith

/-! ### Separated atoms meet strictly negatively -/

/-- For atoms at log-distance `> w`, the cross integrand of the Lévy form is
`−g_m g_n(· + y) − g_m(· + y) g_n`. -/
theorem atom_sub_shift_mul_eq (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {m n : ℕ}
    (hsep : w < |Real.log n - Real.log m|) (y u : ℝ) :
    (atom g m u - atom g m (u + y)) * (atom g n u - atom g n (u + y)) =
      -(atom g m u * atom g n (u + y)) - atom g m (u + y) * atom g n u := by
  have hdisj : ∀ u, atom g m u * atom g n u = 0 := fun u => by
    by_contra h
    have hm : u - Real.log m ∈ Set.Icc 0 w := by
      by_contra h'; exact h (by simp [atom, hgsupp _ h'])
    have hn : u - Real.log n ∈ Set.Icc 0 w := by
      by_contra h'; exact h (by simp [atom, hgsupp _ h'])
    have : |Real.log n - Real.log m| ≤ w := by
      rw [abs_le]; constructor <;> linarith [hm.1, hm.2, hn.1, hn.2]
    linarith
  linear_combination hdisj u + hdisj (u + y)

/-- **Separated atoms meet strictly negatively.** For a nonnegative, nonzero `K`-Lipschitz `C²` bump
supported in `[0, w]` and atoms with `log n − log m > w`, `M(g_m, g_n) < 0`: near `y = log(n/m)`
the translate overlap `∫ g_m g_n(· + y)` stays above `‖g‖²/2`, and the Lévy kernel is positive. -/
theorem markovPair_atom_neg (hg : ContDiff ℝ 2 g)
    (hg0 : ∀ u, 0 ≤ g u) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ u v, |g u - g v| ≤ K * |u - v|) (hG : 0 < ∫ u, g u ^ 2) {m n : ℕ}
    (hmn : w < Real.log n - Real.log m) : markovPair (atom g m) (atom g n) < 0 := by
  set d := Real.log n - Real.log m
  set G := ∫ u, g u ^ 2
  set A := ∫ u, g u
  have hd0 : 0 < d := lt_of_le_of_lt hw hmn
  have hsep : w < |Real.log n - Real.log m| := by rw [abs_of_pos hd0]; exact hmn
  have hA : 0 ≤ A := integral_nonneg hg0
  have hm := contDiff_atom hg m
  have hn := contDiff_atom hg n
  have hmc := hasCompactSupport_atom hgsupp m
  have hnc := hasCompactSupport_atom hgsupp n
  set F := levyMixed (atom g m) (atom g n)
  have hF : IntegrableOn F (Ioi 0) := integrableOn_levyMixed hm hmc hn hnc
  -- the translate overlap: `∫ g_m g_n(· + y) ≥ G − K|y − d| A`
  have hover : ∀ y, G - K * |y - d| * A ≤ ∫ u, atom g m u * atom g n (u + y) := fun y => by
    have hGm : ∫ u, atom g m u ^ 2 = G :=
      integral_sub_right_eq_self (fun u => g u ^ 2) (Real.log m)
    have hAm : ∫ u, atom g m u = A := integral_sub_right_eq_self g (Real.log m)
    have i1 : Integrable fun u => atom g m u ^ 2 := integrable_sq_of_continuous hm.continuous hmc
    have i2 : Integrable fun u => atom g m u := hm.continuous.integrable_of_hasCompactSupport hmc
    have hval : ∫ u, (atom g m u ^ 2 - K * |y - d| * atom g m u) = G - K * |y - d| * A := by
      rw [integral_sub i1 (i2.const_mul _), integral_const_mul, hGm, hAm]
    rw [← hval]
    refine integral_mono (i1.sub (i2.const_mul _))
      (integrable_mul_shift hm.continuous hmc hn.continuous y) fun u => ?_
    have hl := hK (u + y - Real.log n) (u - Real.log m)
    rw [show u + y - Real.log n - (u - Real.log m) = y - d by simp only [d]; ring] at hl
    have hlo : atom g m u - K * |y - d| ≤ atom g n (u + y) := by
      simp only [atom]; linarith [(abs_le.mp hl).1]
    have := hg0 (u - Real.log m)
    simp only [atom] at hlo ⊢
    nlinarith
  -- `F ≤ 0` on `(0, ∞)`
  have hint : ∀ y, ∫ u, (atom g m u - atom g m (u + y)) * (atom g n u - atom g n (u + y)) ≤
      -∫ u, atom g m u * atom g n (u + y) := fun y => by
    rw [← integral_neg]
    refine integral_mono (integrable_sub_shift_mul hm.continuous hmc hn.continuous y)
      (integrable_mul_shift hm.continuous hmc hn.continuous y).neg fun u => ?_
    rw [atom_sub_shift_mul_eq hgsupp hsep]
    have := mul_nonneg (hg0 (u + y - Real.log m)) (hg0 (u - Real.log n))
    simp only [atom] at this ⊢
    linarith
  have hFnp : ∀ y ∈ Ioi (0 : ℝ), F y ≤ 0 := fun y hy => by
    have h1 := hint y
    have h2 : 0 ≤ ∫ u, atom g m u * atom g n (u + y) :=
      integral_nonneg fun u => mul_nonneg (hg0 _) (hg0 _)
    exact mul_nonpos_of_nonneg_of_nonpos (archLevyDensity_pos hy).le (by linarith)
  -- `F ≤ −c` near `y = d`
  set η := min d (G / (2 * (K * A + 1)))
  have hη0 : 0 < η := lt_min hd0 (by positivity)
  have hηG : K * A * η < G / 2 := by
    have h1 : η ≤ G / (2 * (K * A + 1)) := min_le_right _ _
    have h2 : K * A * η ≤ K * A * (G / (2 * (K * A + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : K * A * (G / (2 * (K * A + 1))) < G / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  set c := Real.exp (-(d + η) / 2) * (G / 2)
  have hc : 0 < c := by positivity
  have hFc : ∀ y ∈ Ioc (d - η) (d + η), F y ≤ -c := fun y hy => by
    have hy0 : 0 < y := by linarith [hy.1, min_le_left d (G / (2 * (K * A + 1)))]
    have hyd : |y - d| ≤ η := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have h1 : ∫ u, (atom g m u - atom g m (u + y)) * (atom g n u - atom g n (u + y)) ≤ -(G / 2) := by
      have := hover y
      have : K * |y - d| * A ≤ K * A * η := by
        rw [mul_right_comm]; exact mul_le_mul_of_nonneg_left hyd (by positivity)
      linarith [hint y]
    have hω : Real.exp (-(d + η) / 2) ≤ archLevyDensity y := by
      unfold archLevyDensity
      have hden : 0 < 1 - Real.exp (-2 * y) := by
        have : Real.exp (-2 * y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        linarith
      rw [le_div_iff₀ hden]
      have h2 : Real.exp (-(d + η) / 2) ≤ Real.exp (-y / 2) :=
        Real.exp_le_exp.mpr (by linarith [hy.2])
      nlinarith [Real.exp_pos (-2 * y), Real.exp_pos (-(d + η) / 2)]
    calc F y = archLevyDensity y *
          ∫ u, (atom g m u - atom g m (u + y)) * (atom g n u - atom g n (u + y)) := rfl
      _ ≤ archLevyDensity y * (-(G / 2)) := mul_le_mul_of_nonneg_left h1 (archLevyDensity_pos hy0).le
      _ ≤ Real.exp (-(d + η) / 2) * (-(G / 2)) := mul_le_mul_of_nonpos_right hω (by linarith)
      _ = -c := by simp only [c]; ring
  have hsub : Ioc (d - η) (d + η) ⊆ Ioi 0 := fun y hy => by
    show 0 < y; linarith [hy.1, min_le_left d (G / (2 * (K * A + 1)))]
  have hlevy : ∫ y in Ioi 0, F y < 0 := by
    have hmono : ∫ y in Ioc (d - η) (d + η), -F y ≤ ∫ y in Ioi 0, -F y :=
      setIntegral_mono_set hF.neg
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => by
          simp only [Pi.zero_apply]; linarith [hFnp y hy]))
        hsub.eventuallyLE
    have hbound := setIntegral_mono_on (hF.mono_set hsub) (integrableOn_const (by simp))
      measurableSet_Ioc hFc
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by linarith)] at hbound
    rw [integral_neg, integral_neg] at hmono
    nlinarith
  have hdisj0 : ∫ u, atom g m u * atom g n u = 0 := by
    have : ∀ u, atom g m u * atom g n u = 0 := fun u => by
      have := atom_sub_shift_mul_eq hgsupp hsep 0 u
      simp only [add_zero, sub_self, mul_zero] at this
      linarith [mul_comm (atom g m u) (atom g n u)]
    simp [this]
  have hprime : 0 ≤ primePair (atom g m) (atom g n) := by
    refine tsum_nonneg fun k => mul_nonneg (RHTower.vonMangoldtAtom_nonneg' k) (add_nonneg ?_ ?_) <;>
      exact integral_nonneg fun t => mul_nonneg (hg0 _) (hg0 _)
  show 2 * gammaHardyPhaseRate 0 * (∫ u, atom g m u * atom g n u) + (∫ y in Ioi 0, F y) -
    primePair (atom g m) (atom g n) < 0
  rw [hdisj0, mul_zero, zero_add]
  linarith

/-! ### Dilated bumps -/

/-- The dilated bump `g₁(·/w)` of width `w`. -/
def dilate (g₁ : ℝ → ℝ) (w : ℝ) (u : ℝ) : ℝ := g₁ (u / w)

variable {g₁ : ℝ → ℝ}

theorem contDiff_dilate (hg₁ : ContDiff ℝ 2 g₁) (w : ℝ) : ContDiff ℝ 2 (dilate g₁ w) :=
  hg₁.comp (contDiff_id.div_const w)

theorem dilate_supp (hsupp : ∀ u, u ∉ Set.Icc 0 1 → g₁ u = 0) (hw : 0 < w) :
    ∀ u, u ∉ Set.Icc 0 w → dilate g₁ w u = 0 := fun u hu => by
  apply hsupp
  rintro ⟨h1, h2⟩
  refine hu ⟨?_, (div_le_one hw).mp h2⟩
  have := mul_nonneg h1 hw.le
  rwa [div_mul_cancel₀ _ hw.ne'] at this

theorem hasCompactSupport_dilate (hsupp : ∀ u, u ∉ Set.Icc 0 1 → g₁ u = 0) (hw : 0 < w) :
    HasCompactSupport (dilate g₁ w) :=
  HasCompactSupport.intro isCompact_Icc (dilate_supp hsupp hw)

/-- Dilation by `w` divides the Lipschitz constant by `w`. -/
theorem dilate_lipschitz {L : ℝ} (hL : ∀ u v, |g₁ u - g₁ v| ≤ L * |u - v|) (hw : 0 < w) :
    ∀ u v, |dilate g₁ w u - dilate g₁ w v| ≤ L / w * |u - v| := fun u v => by
  refine (hL _ _).trans (le_of_eq ?_)
  rw [← sub_div, abs_div, abs_of_pos hw]
  ring

/-- `∫ g₁(u/w) g₁((u − s)/w) du = w ∫ g₁(v) g₁(v − s/w) dv`. -/
theorem integral_dilate_mul_shift (hw : 0 < w) (s : ℝ) :
    ∫ u, dilate g₁ w u * dilate g₁ w (u - s) = w * ∫ v, g₁ v * g₁ (v - s / w) := by
  have := Measure.integral_comp_div (fun v => g₁ v * g₁ (v - s / w)) w
  rw [abs_of_pos hw, smul_eq_mul] at this
  rw [← this]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => by simp only [dilate, sub_div])

theorem integral_dilate (hw : 0 < w) : ∫ u, dilate g₁ w u = w * ∫ v, g₁ v := by
  have := Measure.integral_comp_div g₁ w
  rwa [abs_of_pos hw, smul_eq_mul] at this

theorem integral_dilate_sq (hw : 0 < w) : ∫ u, dilate g₁ w u ^ 2 = w * ∫ v, g₁ v ^ 2 := by
  have := Measure.integral_comp_div (fun v => g₁ v ^ 2) w
  rwa [abs_of_pos hw, smul_eq_mul] at this

/-- The overlap `∫ g₁(v) g₁(v − τ) dv` is `L ‖g₁‖₁`-Lipschitz in the shift `τ`. -/
theorem overlap_ge_sub (hg₁ : Continuous g₁) (hg₁c : HasCompactSupport g₁) (hg₁0 : ∀ u, 0 ≤ g₁ u)
    {L : ℝ} (hL : ∀ u v, |g₁ u - g₁ v| ≤ L * |u - v|) (τ τ₀ : ℝ) :
    (∫ v, g₁ v * g₁ (v - τ₀)) - L * |τ - τ₀| * ∫ v, g₁ v ≤ ∫ v, g₁ v * g₁ (v - τ) := by
  have hi : ∀ t : ℝ, Integrable fun v => g₁ v * g₁ (v - t) := fun t => by
    simpa [sub_eq_add_neg] using integrable_mul_shift hg₁ hg₁c hg₁ (-t)
  have i1 : Integrable g₁ := hg₁.integrable_of_hasCompactSupport hg₁c
  rw [← integral_const_mul, ← integral_sub (hi τ₀) (i1.const_mul _)]
  refine integral_mono ((hi τ₀).sub (i1.const_mul _)) (hi τ) fun v => ?_
  have hl := hL (v - τ) (v - τ₀)
  rw [show v - τ - (v - τ₀) = -(τ - τ₀) by ring, abs_neg] at hl
  have := hg₁0 v
  nlinarith [(abs_le.mp hl).1]

/-! ### Close dilated atoms meet positively -/

/-- **Close dilated atoms meet positively.** If the profile overlap at relative shift `τ₀` is
positive, there are `w₀, ε > 0` such that every dilation `g₁(·/w)` with `w < w₀` meets its translate
by `s ≤ w`, `|s − τ₀ w| ≤ ε w`, with positive Markov pairing. -/
theorem exists_markovPair_dilate_shift_pos (hg₁ : ContDiff ℝ 2 g₁) (hg₁c : HasCompactSupport g₁)
    (hg₁0 : ∀ u, 0 ≤ g₁ u) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → g₁ u = 0) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ u v, |g₁ u - g₁ v| ≤ L * |u - v|) {τ₀ : ℝ} (hr : 0 < ∫ v, g₁ v * g₁ (v - τ₀)) :
    ∃ w₀ > 0, ∃ ε > 0, ∀ w s, 0 < w → w < w₀ → 0 < s → s ≤ w → |s - τ₀ * w| ≤ ε * w →
      0 < markovPair (dilate g₁ w) (fun u => dilate g₁ w (u - s)) := by
  set r₀ := ∫ v, g₁ v * g₁ (v - τ₀)
  set A₁ := ∫ v, g₁ v
  set θ := gammaHardyPhaseRate 0
  have hA₁ : 0 ≤ A₁ := integral_nonneg hg₁0
  set T := 4 * Real.exp (1 / 2) * L * A₁ / r₀ - 2 * θ
  refine ⟨min (Real.log 2 / 2) (Real.exp (-T) / 2),
    lt_min (by positivity) (by positivity), r₀ / (2 * (L * A₁ + 1)), by positivity,
    fun w s hw0 hww₀ hs0 hsw hsτ => ?_⟩
  have hw2 : 2 * w < Real.log 2 := by linarith [min_le_left (Real.log 2 / 2) (Real.exp (-T) / 2)]
  have hwT : 2 * w < Real.exp (-T) := by
    linarith [min_le_right (Real.log 2 / 2) (Real.exp (-T) / 2)]
  -- `log(1/(2w)) > T`
  have hlog : T < Real.log (1 / (2 * w)) := by
    rw [one_div, Real.log_inv, lt_neg]
    calc Real.log (2 * w) < Real.log (Real.exp (-T)) := Real.log_lt_log (by positivity) hwT
      _ = -T := Real.log_exp _
  -- the overlap at `s/w` is at least `r₀/2`
  have hτ : |s / w - τ₀| ≤ r₀ / (2 * (L * A₁ + 1)) := by
    rw [show s / w - τ₀ = (s - τ₀ * w) / w by field_simp, abs_div, abs_of_pos hw0,
      div_le_iff₀ hw0]
    exact hsτ
  have hr2 : r₀ / 2 ≤ ∫ v, g₁ v * g₁ (v - s / w) := by
    have h1 := overlap_ge_sub hg₁.continuous hg₁c hg₁0 hL (s / w) τ₀
    have h2 : L * |s / w - τ₀| * A₁ ≤ L * (r₀ / (2 * (L * A₁ + 1))) * A₁ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ hL0) hA₁
    have h3 : L * (r₀ / (2 * (L * A₁ + 1))) * A₁ ≤ r₀ / 2 := by
      rw [show L * (r₀ / (2 * (L * A₁ + 1))) * A₁ = r₀ / 2 * (L * A₁ / (L * A₁ + 1)) by
        field_simp]
      have : L * A₁ / (L * A₁ + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith
    linarith
  -- apply the overlap law to `g₁(·/w)`
  have hbound := markovPair_shift_ge (contDiff_dilate hg₁ w) (hasCompactSupport_dilate hsupp hw0)
    (fun u => hg₁0 _) (dilate_supp hsupp hw0) (div_nonneg hL0 hw0.le) (dilate_lipschitz hL hw0)
    hw0 hw2 hs0.le hsw
  rw [integral_dilate_mul_shift hw0, integral_dilate hw0] at hbound
  set κ := 2 * θ + Real.log (1 / (2 * w))
  have hκ : 4 * Real.exp (1 / 2) * L * A₁ / r₀ < κ := by simp only [κ, T] at hlog ⊢; linarith
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ.le
  have hLw : 2 * Real.exp (1 / 2) * (L / w) * w * (w * A₁) = 2 * Real.exp (1 / 2) * L * A₁ * w := by
    field_simp
  rw [hLw] at hbound
  have key : 2 * Real.exp (1 / 2) * L * A₁ * w < κ * (w * ∫ v, g₁ v * g₁ (v - s / w)) := by
    calc 2 * Real.exp (1 / 2) * L * A₁ * w =
          4 * Real.exp (1 / 2) * L * A₁ / r₀ * (w * (r₀ / 2)) := by field_simp; ring
      _ < κ * (w * (r₀ / 2)) := mul_lt_mul_of_pos_right hκ (by positivity)
      _ ≤ κ * (w * ∫ v, g₁ v * g₁ (v - s / w)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr2 hw0.le) hκ0
  linarith

/-! ### The atom spacing -/

theorem inv_succ_le_atomSpacing {N : ℕ} (hN : 1 ≤ N) : 1 / ((N : ℝ) + 1) ≤ atomSpacing N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + 1 / N by positivity)
  have hinv : 1 - (1 + 1 / (N : ℝ))⁻¹ = 1 / (N + 1) := by
    have : (N : ℝ) + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hinv] at h
  exact h

theorem atomSpacing_le_inv' {N : ℕ} (hN : 1 ≤ N) : atomSpacing N ≤ 1 / N := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / N by positivity)
  unfold atomSpacing
  linarith

/-- The last gap `log N − log(N − 1)` lies between `δ_N` and `1/(N − 1)`. -/
theorem atomSpacing_le_lastGap {N : ℕ} (hN : 2 ≤ N) :
    atomSpacing N ≤ Real.log N - Real.log (N - 1 : ℕ) ∧
      Real.log N - Real.log (N - 1 : ℕ) ≤ 1 / ((N : ℝ) - 1) := by
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  rw [hcast, ← Real.log_div hNpos.ne' h1.ne']
  constructor
  · unfold atomSpacing
    refine Real.log_le_log (by positivity) ?_
    rw [le_div_iff₀ h1]
    have : (1 + 1 / (N : ℝ)) * (N - 1) = N - 1 / N := by field_simp; ring
    rw [this]
    have : (0 : ℝ) < 1 / N := by positivity
    linarith
  · have := Real.log_le_sub_one_of_pos (div_pos hNpos h1)
    have e : (N : ℝ) / (N - 1) - 1 = 1 / (N - 1) := by
      rw [div_sub_one h1.ne']; congr 1; ring
    linarith

/-! ### Beyond the spacing every gauge is frustrated -/

/-- **Beyond the spacing the atomic form is frustrated at every overlap ratio with positive profile
overlap.** For a nonnegative Lipschitz `C²` profile `g₁` supported in `[0, 1]` and an overlap ratio
`ρ > 1` with `∫ g₁(v) g₁(v − 1/ρ) dv > 0`, there is `N₀` such that for every `N ≥ N₀` no unimodular
gauge makes the atom block of the atomic intersection form of `g₁(·/(ρδ_N))` entrywise nonnegative. -/
theorem atomicMarkovGram_dilate_frustrated (hg₁ : ContDiff ℝ 2 g₁) (hg₁c : HasCompactSupport g₁)
    (hg₁0 : ∀ u, 0 ≤ g₁ u) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → g₁ u = 0) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ u v, |g₁ u - g₁ v| ≤ L * |u - v|) {ρ : ℝ} (hρ : 1 < ρ)
    (hr : 0 < ∫ v, g₁ v * g₁ (v - 1 / ρ)) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ¬ ∃ γ : Fin N → ℂ, (∀ i, ‖γ i‖ = 1) ∧
      ∀ i j, i ≠ j → 0 ≤ conj (γ i) * γ j *
        ((-atomicMarkovGram (dilate g₁ (ρ * atomSpacing N)) N i j : ℝ) : ℂ) := by
  obtain ⟨w₀, hw₀, ε, hε, hpos⟩ := exists_markovPair_dilate_shift_pos hg₁ hg₁c hg₁0 hsupp hL0 hL hr
  -- the profile is nonzero
  have hG₁ : 0 < ∫ v, g₁ v ^ 2 := by
    obtain ⟨v, hv⟩ : ∃ v, g₁ v * g₁ (v - 1 / ρ) ≠ 0 := by
      by_contra h
      push Not at h
      simp only [h, integral_zero, lt_self_iff_false] at hr
    have hgc2 : HasCompactSupport fun u => g₁ u ^ 2 := by
      rw [show (fun u => g₁ u ^ 2) = g₁ * g₁ from funext fun u => by simp [sq]]
      exact hg₁c.mul_right
    exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := v)
      (hg₁.continuous.pow 2) hgc2 (fun u => sq_nonneg _)
      (pow_ne_zero 2 (left_ne_zero_of_mul hv))
  set w₁ := min w₀ (Real.log 2 / 2)
  have hw₁ : 0 < w₁ := lt_min hw₀ (by positivity)
  refine ⟨⌈ρ / w₁ + 2 / ε + 2 / (ρ - 1)⌉₊ + 3, fun N hN => ?_⟩
  have hceil := Nat.le_ceil (ρ / w₁ + 2 / ε + 2 / (ρ - 1))
  have hN3 : 3 ≤ N := by omega
  have hNr : (⌈ρ / w₁ + 2 / ε + 2 / (ρ - 1)⌉₊ : ℝ) + 3 ≤ N := by exact_mod_cast hN
  have hρw : 0 ≤ ρ / w₁ := by positivity
  have hεi : 0 ≤ 2 / ε := by positivity
  have hρi : 0 ≤ 2 / (ρ - 1) := div_nonneg (by norm_num) (by linarith)
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  set δ := atomSpacing N
  set w := ρ * δ
  have hδ0 : 0 < δ := atomSpacing_pos (by omega)
  have hw0 : 0 < w := by positivity
  have hδlo := inv_succ_le_atomSpacing (N := N) (by omega)
  have hδhi := atomSpacing_le_inv' (N := N) (by omega)
  obtain ⟨hs_lo, hs_hi⟩ := atomSpacing_le_lastGap (N := N) (by omega)
  set s := Real.log N - Real.log (N - 1 : ℕ)
  -- `w < w₁`
  have hww₁ : w < w₁ := by
    have h1 : w ≤ ρ / N := by
      calc w = ρ * δ := rfl
        _ ≤ ρ * (1 / N) := mul_le_mul_of_nonneg_left hδhi (by linarith)
        _ = ρ / N := by ring
    have h2 : ρ / N < w₁ := by
      rw [div_lt_iff₀ (by linarith)]
      have : ρ / w₁ < N := by linarith
      rwa [div_lt_iff₀ hw₁, mul_comm] at this
    linarith
  have hww₀ : w < w₀ := lt_of_lt_of_le hww₁ (min_le_left _ _)
  -- the last gap is within `ε w` of `δ = w/ρ`, and at most `w`
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hgap : s - δ ≤ 2 / ((N - 1) * (N + 1)) := by
    have : 1 / ((N : ℝ) - 1) - 1 / ((N : ℝ) + 1) = 2 / ((N - 1) * (N + 1)) := by
      rw [div_sub_div _ _ hN1.ne' (by positivity)]; congr 1; ring
    linarith
  have hsmall : ∀ x : ℝ, 0 < x → 2 / x ≤ (N : ℝ) - 1 → s - δ ≤ x * δ := fun x hx hxN => by
    have h1 : 2 / ((N - 1) * (N + 1)) ≤ x / (N + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      rw [div_le_iff₀ hx] at hxN
      nlinarith
    have h2 : x / ((N : ℝ) + 1) ≤ x * δ := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hδlo hx.le
    linarith
  have hsε : s - δ ≤ ε * δ := hsmall ε hε (by linarith)
  have hsρ : s - δ ≤ (ρ - 1) * δ := hsmall (ρ - 1) (by linarith) (by linarith)
  have hsw : s ≤ w := by simp only [w]; nlinarith
  have hs0 : 0 < s := lt_of_lt_of_le hδ0 hs_lo
  have hsτ : |s - 1 / ρ * w| ≤ ε * w := by
    have e : 1 / ρ * w = δ := by simp only [w]; field_simp
    rw [e, abs_of_nonneg (by linarith)]
    have : ε * δ ≤ ε * w := mul_le_mul_of_nonneg_left (by simp only [w]; nlinarith) hε.le
    linarith
  -- the three pairings
  have hg := contDiff_dilate hg₁ w
  have hgc := hasCompactSupport_dilate hsupp hw0
  have hg0 : ∀ u, 0 ≤ dilate g₁ w u := fun u => hg₁0 _
  have hgs := dilate_supp hsupp hw0
  have hGw : 0 < ∫ u, dilate g₁ w u ^ 2 := by rw [integral_dilate_sq hw0]; positivity
  have hlog2 : w < Real.log 2 := by
    have := min_le_right w₀ (Real.log 2 / 2)
    have := Real.log_pos one_lt_two
    linarith
  have hlogN : ∀ n : ℕ, 2 ≤ n → w < Real.log n - Real.log (1 : ℕ) := fun n hn => by
    have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    simp only [Nat.cast_one, Real.log_one, sub_zero]
    linarith
  have h1 : 0 < markovPair (atom (dilate g₁ w) (N - 1)) (atom (dilate g₁ w) N) := by
    rw [markovPair_atom_eq_shift]
    exact hpos w s hw0 hww₀ hs0 hsw hsτ
  have hneg : ∀ n : ℕ, 2 ≤ n → markovPair (atom (dilate g₁ w) 1) (atom (dilate g₁ w) n) < 0 :=
    fun n hn => markovPair_atom_neg hg hg0 hgs hw0.le (div_nonneg hL0 hw0.le)
      (dilate_lipschitz hL hw0) hGw (hlogN n hn)
  exact not_nonneg_gauge_of_odd_triangle_atoms _ hN3 h1 (hneg N (by omega)) (hneg (N - 1) (by omega))

/-- **The Metzler threshold of the overlap ratio is one.** For a nonnegative Lipschitz `C²` profile
`g₁` supported in `[0, 1]` and positive on `(0, 1)`, the atomic intersection form of the bump
`g₁(·/(ρδ_N))`

* is Metzler in the Euler gauge for every overlap ratio `0 < ρ < 1` and every `N ≥ 1`;
* for every `ρ > 1` and all large `N`, admits no unimodular gauge making its atom block Metzler. -/
theorem metzlerThreshold_overlapRatio (hg₁ : ContDiff ℝ 2 g₁) (hg₁c : HasCompactSupport g₁)
    (hg₁0 : ∀ u, 0 ≤ g₁ u) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → g₁ u = 0)
    (hpos : ∀ u ∈ Set.Ioo (0 : ℝ) 1, 0 < g₁ u) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ u v, |g₁ u - g₁ v| ≤ L * |u - v|) :
    (∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ N : ℕ, 1 ≤ N →
      IsMetzler (atomicIntersectionGram (dilate g₁ (ρ * atomSpacing N)) N)) ∧
    (∀ ρ : ℝ, 1 < ρ → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ¬ ∃ γ : Fin N → ℂ, (∀ i, ‖γ i‖ = 1) ∧
      ∀ i j, i ≠ j → 0 ≤ conj (γ i) * γ j *
        ((-atomicMarkovGram (dilate g₁ (ρ * atomSpacing N)) N i j : ℝ) : ℂ)) := by
  refine ⟨fun ρ hρ0 hρ1 N hN => ?_, fun ρ hρ => ?_⟩
  · have hδ := atomSpacing_pos hN
    exact atomicIntersectionGram_isMetzler (fun u => hg₁0 _)
      (dilate_supp hsupp (by positivity)) (by nlinarith)
  · refine atomicMarkovGram_dilate_frustrated hg₁ hg₁c hg₁0 hsupp hL0 hL hρ ?_
    -- the profile overlap at `1/ρ < 1` is positive at the midpoint of `(1/ρ, 1)`
    have hτ0 : 0 < 1 / ρ := by positivity
    have hτ1 : 1 / ρ < 1 := by rw [div_lt_one (by linarith)]; exact hρ
    have hc : Continuous fun v => g₁ v * g₁ (v - 1 / ρ) :=
      hg₁.continuous.mul (hg₁.continuous.comp (continuous_id.sub continuous_const))
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 + 1 / ρ) / 2) hc
      hg₁c.mul_right (fun v => mul_nonneg (hg₁0 _) (hg₁0 _)) ?_
    exact mul_ne_zero (hpos _ ⟨by linarith, by linarith⟩).ne'
      (hpos _ ⟨by linarith, by linarith⟩).ne'

end GaloisForLFunctions.ArithmeticLorentzianGeometry
