import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OneProbeSeesEveryOuterEigenvalue
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OnePrimeSeesTheWholeDefectOfZeta

/-!
# One test carries the whole defect of `ζ` at each prime

`OnePrimeSeesTheWholeDefectOfZeta` lets the test depend on the number of negative squares it
should produce. Here a single test does it: for every deep-sparse configuration and every scale
`ℓ` there is one `C²` compactly supported test whose tower has, on some window, `n` negative
squares iff there are at least `n` distinct outer eigenvalues (`deepSparse_exists_test_tower_law`).
For `ζ` this holds at every prime (`zeta_exists_test_onePrime_tower_law`), and one test's
`p`-tower decides RH (`zeta_exists_test_riemannHypothesis_iff`).

The proof splits by depth.

* **Finitely many eigenvalues at each depth.** Inside every disc `‖z‖ < r < 1` the folded spectrum
  of any test has finitely many points, so every outer eigenvalue is accessible
  (`accessibleOff_of_finite_deep`); the probe of `OneProbeSeesEveryOuterEigenvalue` makes every one
  visible (`exists_test_reach_of_deep_finite`).
* **Infinitely many eigenvalues at a depth `δ`.** Their reciprocals accumulate; a sequence with
  `|u_{n+1} − x| < |u_n − x|/3` keeps each `u_n` isolated and adds only `x` to its closure
  (`exists_separated_seq`). The test killing every right zero of depth `≥ δ/2` except one
  representative of each `u_n⁻¹` gives each `u_n⁻¹` a single weight term, and near the origin its
  folded spectrum lies in the sequence and its limit (`exists_test_reach_of_deep_infinite`).
-/

open Complex Filter Topology Set Metric
open scoped ComplexConjugate Classical lp
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### 1. Separated accumulating sequences -/

/-- **A separated accumulating sequence.** An infinite bounded set of complex numbers contains a
sequence `u_n → x` with `|u_{n+1} − x| < |u_n − x|/3`: it is injective, its closure adds only `x`,
and each `u_n` is isolated in `{x} ∪ {u_m}`. -/
theorem exists_separated_seq {S : Set ℂ} (hS : S.Infinite) (hb : Bornology.IsBounded S) :
    ∃ (u : ℕ → ℂ) (x : ℂ), (∀ n, u n ∈ S) ∧ Function.Injective u ∧
      closure (Set.range u) ⊆ insert x (Set.range u) ∧
      ∀ n, ∃ ε > 0, ∀ z ∈ insert x (Set.range u), ‖z - u n‖ < ε → z = u n := by
  obtain ⟨x, -, hx⟩ := hS.exists_accPt_of_subset_isCompact hb.isCompact_closure subset_closure
  have hacc : ∀ ε : ℝ, 0 < ε → ∃ z, z ∈ S ∧ z ≠ x ∧ dist z x < ε := by
    intro ε hε
    obtain ⟨y, ⟨hyU, hyS⟩, hyx⟩ := accPt_iff_nhds.mp hx (ball x ε) (ball_mem_nhds x hε)
    exact ⟨y, hyS, hyx, hyU⟩
  choose! pick hpickS hpickx hpickd using hacc
  set u : ℕ → ℂ := fun n => Nat.rec (motive := fun _ => ℂ) (pick 1)
    (fun _ z => pick (dist z x / 3)) n
  have hu0 : u 0 = pick 1 := rfl
  have husucc : ∀ n, u (n + 1) = pick (dist (u n) x / 3) := fun n => rfl
  have hpos : ∀ n, u n ∈ S ∧ 0 < dist (u n) x := by
    intro n
    induction n with
    | zero => exact ⟨hpickS 1 one_pos, dist_pos.mpr (hpickx 1 one_pos)⟩
    | succ n ih =>
      have hε : 0 < dist (u n) x / 3 := by linarith [ih.2]
      rw [husucc]
      exact ⟨hpickS _ hε, dist_pos.mpr (hpickx _ hε)⟩
  have hdec : ∀ n, dist (u (n + 1)) x < dist (u n) x / 3 := fun n => by
    rw [husucc]
    exact hpickd _ (by linarith [(hpos n).2])
  -- later terms are three times closer
  have hfar : ∀ n m, n < m → dist (u m) x < dist (u n) x / 3 := by
    intro n m hnm
    have hnm' : n + 1 ≤ m := hnm
    clear hnm
    induction m, hnm' using Nat.le_induction with
    | base => exact hdec n
    | succ m hm ih => exact (hdec m).trans (by linarith [(hpos m).2, (hpos n).2])
  have hinj : Function.Injective u := by
    intro m n hmn
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := hfar m n h
      rw [hmn] at h1
      linarith [(hpos n).2]
    · have h1 := hfar n m h
      rw [hmn] at h1
      linarith [(hpos n).2]
  have hgeo : ∀ n, dist (u n) x ≤ dist (u 0) x * (1 / 3) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      linarith [hdec n]
  have htend : Tendsto u atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) hgeo ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num)).const_mul (dist (u 0) x)
  have hcl : closure (Set.range u) ⊆ insert x (Set.range u) :=
    closure_minimal (Set.subset_insert _ _) htend.isCompact_insert_range.isClosed
  refine ⟨u, x, fun n => (hpos n).1, hinj, hcl, fun n =>
    ⟨dist (u n) x / 2, by linarith [(hpos n).2], fun z hz hlt => ?_⟩⟩
  rcases hz with hzx | ⟨m, rfl⟩
  · exfalso
    rw [hzx, ← dist_eq_norm, dist_comm x (u n)] at hlt
    linarith [(hpos n).2]
  · rcases lt_trichotomy m n with h | rfl | h
    · exfalso
      have h1 := hfar m n h
      have h2 := dist_triangle (u m) (u n) x
      rw [dist_eq_norm (u m) (u n)] at h2
      linarith [(hpos n).2, (hpos m).2]
    · rfl
    · exfalso
      have h1 := hfar n m h
      have h2 := dist_triangle (u n) (u m) x
      rw [dist_comm (u n) (u m), dist_eq_norm (u m) (u n)] at h2
      linarith [(hpos n).2]

/-! ### 2. The folded spectrum near the origin -/

/-- The folded spectrum stays at modulus `≥ e^{−ℓ/2}`. -/
theorem closure_activeFoldedSpectrum_subset (Z : ZeroConfig) (g : ℝ → ℂ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    closure (activeFoldedSpectrum Z g ℓ) ⊆ {z : ℂ | Real.exp (-(ℓ / 2)) ≤ ‖z‖} := by
  refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
  rintro z ⟨τ, hτ, -, rfl⟩
  show Real.exp (-(ℓ / 2)) ≤ ‖(frobEig ℓ τ)⁻¹‖
  rw [norm_inv, norm_frobEig, ← Real.exp_neg, Real.exp_le_exp]
  have := (Z.strip _ hτ).2
  nlinarith

theorem zero_notMem_closure_activeFoldedSpectrum (Z : ZeroConfig) (g : ℝ → ℂ) {ℓ : ℝ}
    (hℓ : 0 < ℓ) : (0 : ℂ) ∉ closure (activeFoldedSpectrum Z g ℓ) := fun h => by
  have h' := closure_activeFoldedSpectrum_subset Z g hℓ h
  simp only [Set.mem_setOf_eq, norm_zero] at h'
  exact absurd h' (not_le.mpr (Real.exp_pos _))

/-- **Finitely many eigenvalues at each depth make every eigenvalue accessible.** Inside a disc
`‖z‖ < r < 1` the folded spectrum of any test lies in the finitely many reciprocal eigenvalues of
depth `≥ −log r/ℓ`. -/
theorem accessibleOff_of_finite_deep {Z : ZeroConfig} {g : ℝ → ℂ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hfin : ∀ δ : ℝ, 0 < δ → {b ∈ outerEig Z ℓ | Real.exp (ℓ * δ) ≤ ‖b‖}.Finite) {b : ℂ}
    (hb : b ∈ outerEig Z ℓ) : AccessibleOff (closure (activeFoldedSpectrum Z g ℓ)) b⁻¹ := by
  obtain ⟨ρ, hρ, rfl⟩ := hb
  have hw1 : ‖(frobEig ℓ ρ)⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ ((one_lt_norm_frobEig_iff hℓ ρ).mpr hρ.2)
  set r : ℝ := (‖(frobEig ℓ ρ)⁻¹‖ + 1) / 2 with hrdef
  have hr : ‖(frobEig ℓ ρ)⁻¹‖ < r := by rw [hrdef]; linarith
  have hr1 : r < 1 := by rw [hrdef]; linarith
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr
  set δ : ℝ := -Real.log r / ℓ with hδdef
  have hδ : 0 < δ := div_pos (neg_pos.mpr (Real.log_neg hr0 hr1)) hℓ
  have hexpδ : Real.exp (ℓ * δ) = r⁻¹ := by
    rw [hδdef, mul_div_cancel₀ _ hℓ.ne', Real.exp_neg, Real.exp_log hr0]
  set P : Set ℂ := (fun b => b⁻¹) '' {b ∈ outerEig Z ℓ | Real.exp (ℓ * δ) ≤ ‖b‖}
  have hPfin : P.Finite := (hfin δ hδ).image _
  have hsubP : ball (0 : ℂ) r ∩ activeFoldedSpectrum Z g ℓ ⊆ P := by
    rintro z ⟨hzr, τ, hτ, -, rfl⟩
    rw [mem_ball_zero_iff, norm_inv] at hzr
    have hβ : r⁻¹ < ‖frobEig ℓ τ‖ :=
      (inv_lt_comm₀ (norm_pos_iff.mpr (frobEig_ne_zero ℓ τ)) hr0).mp hzr
    have h1 : 1 < ‖frobEig ℓ τ‖ := lt_trans ((one_lt_inv₀ hr0).mpr hr1) hβ
    exact ⟨frobEig ℓ τ, ⟨⟨τ, ⟨hτ, (one_lt_norm_frobEig_iff hℓ τ).mp h1⟩, rfl⟩,
      by rw [hexpδ]; exact hβ.le⟩, rfl⟩
  have hcl : ball (0 : ℂ) r ∩ closure (activeFoldedSpectrum Z g ℓ) ⊆ P :=
    isOpen_ball.inter_closure.trans ((closure_mono hsubP).trans hPfin.isClosed.closure_subset)
  have hP' : (P \ {(frobEig ℓ ρ)⁻¹}).Finite := hPfin.subset Set.sdiff_subset
  obtain ⟨ε, hε, hεP⟩ := Metric.isOpen_iff.mp hP'.isClosed.isOpen_compl (frobEig ℓ ρ)⁻¹
    (by simp)
  refine accessibleOff_of_countable isClosed_closure hr0
    ((hPfin.subset fun z hz => hcl ⟨hz.2, hz.1⟩).countable)
    (zero_notMem_closure_activeFoldedSpectrum Z g hℓ) hr (lt_min hε (sub_pos.mpr hr))
    fun z hz hzlt => ?_
  have hzr : z ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff]
    calc ‖z‖ = ‖(z - (frobEig ℓ ρ)⁻¹) + (frobEig ℓ ρ)⁻¹‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - (frobEig ℓ ρ)⁻¹‖ + ‖(frobEig ℓ ρ)⁻¹‖ := norm_add_le _ _
      _ < r := by linarith [hzlt.trans_le (min_le_right _ _)]
  by_contra hne
  exact hεP (by rw [mem_ball, dist_eq_norm]; exact hzlt.trans_le (min_le_left _ _))
    ⟨hcl ⟨hzr, hz⟩, hne⟩

/-! ### 3. One test for every count -/

/-- **Finitely many eigenvalues at each depth: a probe reaches every count.** -/
theorem exists_test_reach_of_deep_finite (Z : ZeroConfig) (hZ : TemperedConfig Z) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hfin : ∀ δ : ℝ, 0 < δ → {b ∈ outerEig Z ℓ | Real.exp (ℓ * δ) ≤ ‖b‖}.Finite) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ n : ℕ,
      (n : ℕ∞) ≤ (outerEig Z ℓ).encard → ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K) := by
  have hR : (rightZeros Z).Countable :=
    (SquareRootThreshold.countable_carrier Z).mono fun _ h => h.1
  set B : Set ℝ := ⋃ b ∈ outerEig Z ℓ, {s : ℝ | frobWeight Z (probe s 0) ℓ b = 0}
  have hB : B.Countable := (hR.image _).biUnion fun b hb => countable_badModulation Z hZ hℓ hb
  obtain ⟨s, hs⟩ : ∃ s, s ∉ B := by
    by_contra h
    push Not at h
    exact Cardinal.not_countable_real (hB.mono fun s _ => h s)
  refine ⟨probe s 0, probe_contDiff s 0, probe_hasCompactSupport s 0, fun n hn => ?_⟩
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq hn
  have htfin : t.Finite := Set.finite_of_encard_eq_coe htc
  obtain ⟨K, hK⟩ := card_le_towerDefect_of_accessibleOff Z hZ (probe_contDiff s 0)
    (probe_hasCompactSupport s 0) hℓ htfin.toFinset
    (fun b hb => ⟨hts (htfin.mem_toFinset.mp hb),
      fun h0 => hs (Set.mem_biUnion (hts (htfin.mem_toFinset.mp hb)) h0)⟩)
    fun b hb => accessibleOff_of_finite_deep hℓ hfin (hts (htfin.mem_toFinset.mp hb))
  have hcard : htfin.toFinset.card = n := by
    have h := htfin.encard_eq_coe_toFinset_card
    rw [htc] at h
    exact_mod_cast h.symm
  exact ⟨K, hcard ▸ hK⟩

/-- **Infinitely many eigenvalues at a depth: one killing test reaches every count.** -/
theorem exists_test_reach_of_deep_infinite (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hQ : ∃ δ : ℝ, 0 < δ ∧ {b ∈ outerEig Z ℓ | Real.exp (ℓ * δ) ≤ ‖b‖}.Infinite) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ n : ℕ,
      (n : ℕ∞) ≤ (outerEig Z ℓ).encard → ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K) := by
  obtain ⟨δ, hδ, hD⟩ := hQ
  set D := {b ∈ outerEig Z ℓ | Real.exp (ℓ * δ) ≤ ‖b‖}
  set S : Set ℂ := (fun b => b⁻¹) '' D
  have hSinf : S.Infinite := hD.image inv_injective.injOn
  have hSb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset ?_
    rintro z ⟨b, ⟨⟨ρ, hρ, rfl⟩, -⟩, rfl⟩
    rw [mem_closedBall_zero_iff, norm_inv]
    exact (inv_lt_one_of_one_lt₀ ((one_lt_norm_frobEig_iff hℓ ρ).mpr hρ.2)).le
  obtain ⟨u, x, huS, huinj, hucl, husep⟩ := exists_separated_seq hSinf hSb
  have hrep : ∀ b ∈ outerEig Z ℓ, ∃ ρ, ρ ∈ rightZeros Z ∧ frobEig ℓ ρ = b := fun b hb => hb
  choose! rep hrepR hrepb using hrep
  set bseq : ℕ → ℂ := fun n => (u n)⁻¹
  have hbD : ∀ n, bseq n ∈ D := fun n => by
    obtain ⟨b, hb, hbu⟩ := huS n
    have h : bseq n = b := by simp only [bseq, ← hbu, inv_inv]
    rw [h]
    exact hb
  set F : Set ℂ := Set.range fun n => rep (bseq n)
  have hFr : ∀ τ ∈ F, τ ∈ rightZeros Z := by
    rintro τ ⟨n, rfl⟩
    exact hrepR _ (hbD n).1
  have hσ : 1 / 2 < 1 / 2 + δ / 2 := by linarith
  obtain ⟨g, hg, hgc, hkill, hkeep⟩ := exists_test_killing_deep_zeros Z hsp hσ F hFr
  refine ⟨g, hg, hgc, fun n _ => ?_⟩
  -- every `bseq m` is visible through its representative
  have hvis : ∀ m, bseq m ∈ visibleSet Z g ℓ := by
    intro m
    have hbm := hbD m
    refine ⟨hbm.1, frobWeight_ne_zero_of_single Z (hrepR _ hbm.1) (hrepb _ hbm.1)
      (hkeep _ ⟨m, rfl⟩) fun τ hτ hne he => ?_⟩
    have hre : τ.re = (rep (bseq m)).re :=
      re_eq_of_norm_frobEig_eq hℓ (by rw [he, hrepb _ hbm.1])
    have hdeep : 1 / 2 + δ ≤ τ.re := by
      have h1 := hbm.2
      rw [← hrepb _ hbm.1, norm_frobEig, Real.exp_le_exp] at h1
      rw [hre]
      nlinarith
    have hτr : τ ∈ rightZeros Z := ⟨hτ, by linarith⟩
    refine (hkill τ hτr (by linarith) fun hmF => hne ?_).1
    obtain ⟨k, hk⟩ := hmF
    have hk' : rep (bseq k) = τ := hk
    have hkm : bseq k = bseq m := by
      have h := hrepb _ (hbD k).1
      rw [hk'] at h
      rw [← h, he]
    have hkm' : k = m := huinj (inv_injective hkm)
    rw [← hk', hkm']
  -- every `bseq m⁻¹ = u m` is accessible
  have hacc : ∀ m, AccessibleOff (closure (activeFoldedSpectrum Z g ℓ)) (bseq m)⁻¹ := by
    intro m
    have hr0 : 0 < Real.exp (-(ℓ * δ / 2)) := Real.exp_pos _
    have hsub : ball (0 : ℂ) (Real.exp (-(ℓ * δ / 2))) ∩ activeFoldedSpectrum Z g ℓ ⊆
        Set.range u := by
      rintro z ⟨hzr, τ, hτ, hact, rfl⟩
      rw [mem_ball_zero_iff, norm_inv, norm_frobEig, ← Real.exp_neg, Real.exp_lt_exp] at hzr
      have hτre : 1 / 2 + δ / 2 < τ.re := by nlinarith
      have hτr : τ ∈ rightZeros Z := ⟨hτ, by linarith⟩
      by_cases hτF : τ ∈ F
      · obtain ⟨k, hk⟩ := hτF
        have hk' : rep (bseq k) = τ := hk
        refine ⟨k, ?_⟩
        rw [← hk', hrepb _ (hbD k).1]
        simp only [bseq, inv_inv]
      · exfalso
        have h0 := hkill τ hτr hτre.le hτF
        rw [gammaOf_reflect] at h0
        rcases hact with h | h
        · exact h h0.1
        · exact h h0.2
    have hcl : ball (0 : ℂ) (Real.exp (-(ℓ * δ / 2))) ∩ closure (activeFoldedSpectrum Z g ℓ) ⊆
        insert x (Set.range u) :=
      isOpen_ball.inter_closure.trans ((closure_mono hsub).trans hucl)
    have hum : (bseq m)⁻¹ = u m := by simp only [bseq, inv_inv]
    have hunorm : ‖(bseq m)⁻¹‖ < Real.exp (-(ℓ * δ / 2)) := by
      have h1 := (hbD m).2
      rw [norm_inv]
      calc ‖bseq m‖⁻¹ ≤ (Real.exp (ℓ * δ))⁻¹ := inv_anti₀ (Real.exp_pos _) h1
        _ = Real.exp (-(ℓ * δ)) := (Real.exp_neg _).symm
        _ < Real.exp (-(ℓ * δ / 2)) := Real.exp_lt_exp.mpr (by nlinarith)
    obtain ⟨ε, hε, hεsep⟩ := husep m
    refine accessibleOff_of_countable isClosed_closure hr0
      ((((Set.countable_range u).insert x).mono fun z hz => hcl ⟨hz.2, hz.1⟩))
      (zero_notMem_closure_activeFoldedSpectrum Z g hℓ) hunorm (lt_min hε (sub_pos.mpr hunorm))
      fun z hz hzlt => ?_
    have hzr : z ∈ ball (0 : ℂ) (Real.exp (-(ℓ * δ / 2))) := by
      rw [mem_ball_zero_iff]
      calc ‖z‖ = ‖(z - (bseq m)⁻¹) + (bseq m)⁻¹‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - (bseq m)⁻¹‖ + ‖(bseq m)⁻¹‖ := norm_add_le _ _
        _ < Real.exp (-(ℓ * δ / 2)) := by linarith [hzlt.trans_le (min_le_right _ _)]
    rw [hum] at hzlt ⊢
    exact hεsep z (hcl ⟨hzr, hz⟩) (hzlt.trans_le (min_le_left _ _))
  -- the first `n` terms
  have hbinj : Function.Injective bseq := fun a b h => huinj (inv_injective h)
  set O : Finset ℂ := (Finset.range n).image bseq
  have hO : O.card = n := by rw [Finset.card_image_of_injective _ hbinj, Finset.card_range]
  obtain ⟨K, hK⟩ := card_le_towerDefect_of_accessibleOff Z hZ hg hgc hℓ O
    (fun b hb => by obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hb; exact hvis m)
    (fun b hb => by obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hb; exact hacc m)
  exact ⟨K, hO ▸ hK⟩

/-- **One test carries the whole defect at a scale.** For a deep-sparse configuration and every
`ℓ > 0` there is one `C²` compactly supported test such that some window of its tower has `n`
negative squares iff there are at least `n` distinct outer eigenvalues at scale `ℓ`. -/
theorem deepSparse_exists_test_tower_law (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hsp : DeepSparse Z) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ n : ℕ,
      (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔
        (n : ℕ∞) ≤ (outerEig Z ℓ).encard := by
  suffices h : ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ n : ℕ,
      (n : ℕ∞) ≤ (outerEig Z ℓ).encard → ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K) by
    obtain ⟨g, hg, hgc, hreach⟩ := h
    refine ⟨g, hg, hgc, fun n => ⟨fun ⟨K, hK⟩ => ?_, hreach n⟩⟩
    have hs := (wfVisibleSet_sandwich_and_infinite_law Z hZ hg hgc hℓ).2.1 K
    exact (ENat.coe_le_coe.mpr hK).trans (hs.1.trans hs.2)
  by_cases hQ : ∃ δ : ℝ, 0 < δ ∧ {b ∈ outerEig Z ℓ | Real.exp (ℓ * δ) ≤ ‖b‖}.Infinite
  · exact exists_test_reach_of_deep_infinite Z hZ hsp hℓ hQ
  · exact exists_test_reach_of_deep_finite Z hZ hℓ fun δ hδ =>
      Set.not_infinite.mp fun h => hQ ⟨δ, hδ, h⟩

/-! ### 4. `ζ` -/

/-- **One test carries the whole defect of `ζ` at each prime.** For every prime `p` there is one
test whose `p`-tower has, on some window, `n` negative squares iff `ζ` has at least `n` distinct
outer eigenvalues `p^{ρ−½}`. -/
theorem zeta_exists_test_onePrime_tower_law {p : ℕ} (hp : p.Prime) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ ∀ n : ℕ,
      (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram zetaZeroConfig g (Real.log p) K)) ↔
        (n : ℕ∞) ≤ (outerEig zetaZeroConfig (Real.log p)).encard :=
  deepSparse_exists_test_tower_law _ temperedConfig_zetaZeroConfig deepSparse_zeta
    (Real.log_pos (by exact_mod_cast hp.one_lt))

/-- **One test's tower decides RH.** For every prime `p` there is one test `g` such that RH holds
iff Weil's form is positive semidefinite on every finite window of the `p`-tower of `g`. -/
theorem zeta_exists_test_riemannHypothesis_iff {p : ℕ} (hp : p.Prime) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (RiemannHypothesis ↔ ∀ K : Finset ℤ,
        hermNegIndex (towerGram zetaZeroConfig g (Real.log p) K) = 0) := by
  obtain ⟨g, hg, hgc, hlaw⟩ := zeta_exists_test_onePrime_tower_law hp
  refine ⟨g, hg, hgc, ?_⟩
  rw [← rightZeros_zeta_eq_empty_iff]
  constructor
  · intro hR K
    by_contra hne
    have h1 := (hlaw 1).mp ⟨K, Nat.one_le_iff_ne_zero.mpr hne⟩
    have h0 : outerEig zetaZeroConfig (Real.log p) = ∅ := by simp [outerEig, hR]
    rw [h0, Set.encard_empty] at h1
    exact absurd h1 (by norm_num)
  · intro hpsd
    by_contra hne
    obtain ⟨ρ, hρ⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨K, hK⟩ := (hlaw 1).mpr (Set.one_le_encard_iff_nonempty.mpr ⟨_, ρ, hρ, rfl⟩)
    rw [hpsd K] at hK
    exact absurd hK (by norm_num)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
