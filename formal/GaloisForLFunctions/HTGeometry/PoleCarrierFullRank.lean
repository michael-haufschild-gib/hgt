import GaloisForLFunctions.HTGeometry.MonotoneStaircaseJetBox

/-!
# Full-rank node packets for any carrier with a real pole sequence

The blow-up mechanism never used the moving canonical carrier as such.  Four facts about it carried
everything: its translated jets are analytic above the real axis, none of them vanishes identically,
each of them blows up at the prescribed rate at the carrier's poles, and the poles are separated —
consecutive ones by more than `1/2` less than their index gap.

`PoleCarrier` bundles exactly those four facts.  Everything downstream — the pointwise integer
grading, the sign law, the spaced-ray sampling that makes the row-by-shift family collision-free —
is then a theorem about an arbitrary such carrier.

The moving canonical logarithmic derivative is one instance.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The integer rate vector for a distinguished shift group: every jet at the distinguished shift
blows up at its own order, every other jet is renormalized by its vanishing order. -/
noncomputable def integerTranslateJetGroupRate {n : ℕ} (m : Fin n → ℕ) (σ : Fin n → ℂ)
    (k₀ : Fin n) (V : Fin n → ℕ) : Fin n → ℤ :=
  fun k => if σ k = σ k₀ then ((m k : ℤ) + 1) else -(V k : ℤ)

theorem integerTranslateJetGroupRate_pos {n : ℕ} (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n)
    (V : Fin n → ℕ) {k : Fin n} (hk : σ k = σ k₀) :
    0 < integerTranslateJetGroupRate m σ k₀ V k := by
  rw [integerTranslateJetGroupRate, if_pos hk]
  positivity

theorem integerTranslateJetGroupRate_nonpos {n : ℕ} (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n)
    (V : Fin n → ℕ) {k : Fin n} (hk : σ k ≠ σ k₀) :
    integerTranslateJetGroupRate m σ k₀ V k ≤ 0 := by
  rw [integerTranslateJetGroupRate, if_neg hk]
  exact neg_nonpos.mpr (Int.natCast_nonneg _)

/-- A carrier whose translated jets blow up at a separated real sequence.  These are the only
properties of the carrier that the full-rank mechanism consumes. -/
structure PoleCarrier where
  /-- The carrier function. -/
  carrier : ℂ → ℂ
  /-- The real sequence at which the jets blow up. -/
  pole : ℕ → ℝ
  /-- Poles with a given index gap are separated by more than that gap minus `1/2`. -/
  gap : ∀ a b : ℕ, a < b → ((b : ℝ) - (a : ℝ)) - 1 / 2 < pole b - pole a
  /-- Translated jets are analytic wherever the translate lies in the open upper half-plane. -/
  analyticJet : ∀ (r : ℕ) (σ ζ : ℂ), 0 < (ζ + σ).im →
    AnalyticAt ℂ (fun w => iteratedDeriv r carrier (w + σ)) ζ
  /-- Every jet blows up at every pole, at the rate of its order. -/
  jetBlowUp : ∀ (p r : ℕ) (σ : ℂ) (u : ℕ → ℂ), (∀ j, 0 < (u j + σ).im) →
    Tendsto u atTop (𝓝 ((pole p : ℂ) - σ)) →
    ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun j => iteratedDeriv r carrier (u j + σ) *
      (u j - ((pole p : ℂ) - σ)) ^ (r + 1)) atTop (𝓝 c)

namespace PoleCarrier

variable (C : PoleCarrier)

theorem pole_strictMono : StrictMono C.pole := by
  intro a b hab
  have hgap := C.gap a b hab
  have hstep : ((a : ℝ) + 1) ≤ (b : ℝ) := by exact_mod_cast hab
  linarith

theorem pole_injective : Function.Injective C.pole := C.pole_strictMono.injective

/-- **Blow-up forces nonvanishing.**  A jet that blows up at a pole cannot vanish identically near
it, so no separate nondegeneracy assumption is needed. -/
theorem jetNeZero (r : ℕ) : ∃ z : ℂ, 0 < z.im ∧ iteratedDeriv r C.carrier z ≠ 0 := by
  obtain ⟨u, -, hune, huim, hulim, -⟩ := exists_verticalApproach
    (S := (Set.univ : Set ℂ)) (ζ := (C.pole 0 : ℂ) - 0) (ε := 1) one_pos
    (fun y _ _ => Set.mem_univ _)
  have hζim : ((C.pole 0 : ℂ) - 0).im = 0 := by simp
  have hupper : ∀ j, 0 < (u j + 0).im := by
    intro j
    have h1 : (u j + 0).im = (u j - ((C.pole 0 : ℂ) - 0)).im + ((C.pole 0 : ℂ) - 0).im := by
      simp only [Complex.add_im, Complex.sub_im, Complex.zero_im]
      ring
    rw [h1, hζim, add_zero]
    exact huim j
  obtain ⟨c, hcne, hc⟩ := C.jetBlowUp 0 r 0 u hupper hulim
  obtain ⟨j, hj⟩ := (hc.eventually (eventually_ne_nhds hcne)).exists
  refine ⟨u j + 0, hupper j, ?_⟩
  exact left_ne_zero_of_mul hj

/-! ## Finite jet orders -/

/-- No translated jet vanishes identically near the real axis, so its analytic order is finite. -/
theorem analyticOrderAt_jet_ne_top (r : ℕ) {σ ζ : ℂ} (hζ : -σ.im < ζ.im) :
    analyticOrderAt (fun w => iteratedDeriv r C.carrier (w + σ)) ζ ≠ ⊤ := by
  set U : Set ℂ := {w : ℂ | -σ.im < w.im} with hU
  have hUconv : Convex ℝ U := convex_halfSpace_im_gt (-σ.im)
  have hana : ∀ w ∈ U, AnalyticAt ℂ (fun v => iteratedDeriv r C.carrier (v + σ)) w := by
    intro w hw
    refine C.analyticJet r σ w ?_
    have hw' : -σ.im < w.im := hw
    simp only [Complex.add_im]
    linarith
  obtain ⟨z₀, hz₀im, hz₀ne⟩ := C.jetNeZero r
  have hw₀U : z₀ - σ ∈ U := by
    show -σ.im < (z₀ - σ).im
    simp only [Complex.sub_im]
    linarith
  intro htop
  have hev : (fun w => iteratedDeriv r C.carrier (w + σ)) =ᶠ[𝓝 ζ] 0 :=
    analyticOrderAt_eq_top.mp htop
  have hanaOn : AnalyticOnNhd ℂ (fun v => iteratedDeriv r C.carrier (v + σ)) U := hana
  have hzero := hanaOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hUconv.isPreconnected (show ζ ∈ U from hζ) hev
  have hval := hzero hw₀U
  simp only [Pi.zero_apply, sub_add_cancel] at hval
  exact hz₀ne hval

/-- The vanishing order of a translated jet at a point. -/
noncomputable def jetOrder (r : ℕ) (σ ζ : ℂ) : ℕ :=
  (analyticOrderAt (fun w => iteratedDeriv r C.carrier (w + σ)) ζ).toNat

theorem analyticOrderAt_jet_eq (r : ℕ) {σ ζ : ℂ} (hζ : -σ.im < ζ.im) :
    analyticOrderAt (fun w => iteratedDeriv r C.carrier (w + σ)) ζ
      = ((C.jetOrder r σ ζ : ℕ) : ℕ∞) :=
  (ENat.coe_toNat (C.analyticOrderAt_jet_ne_top r hζ)).symm

/-! ## The blow-up datum -/

set_option maxHeartbeats 1000000 in
/-- **The blow-up datum with a whole group at the distinguished shift.** -/
theorem exists_groupBlowUp_at {n : ℕ} (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n) (V : Fin n → ℕ)
    {S : Set ℂ} {ζ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hS : ∀ y : ℝ, 0 < y → y < ε → ζ + (y : ℂ) * Complex.I ∈ S)
    (hzero : ∃ p : ℕ, ζ = (C.pole p : ℂ) - σ k₀)
    (hfin : ∀ k, σ k ≠ σ k₀ →
      AnalyticAt ℂ (fun w => iteratedDeriv (m k) C.carrier (w + σ k)) ζ)
    (hV : ∀ k, σ k ≠ σ k₀ →
      analyticOrderAt (fun w => iteratedDeriv (m k) C.carrier (w + σ k)) ζ = ((V k : ℕ) : ℕ∞)) :
    ∃ (u : ℕ → ℂ) (t : ℕ → ℂ) (c : Fin n → ℂ),
      (∀ j, u j ∈ S) ∧ (∀ j, t j ≠ 0) ∧ Tendsto u atTop (𝓝 ζ) ∧ Tendsto t atTop (𝓝 0) ∧
        (∀ k, c k ≠ 0) ∧
        ∀ k, Tendsto (fun j => iteratedDeriv (m k) C.carrier (u j + σ k) *
            t j ^ (integerTranslateJetGroupRate m σ k₀ V k)) atTop (𝓝 (c k)) := by
  classical
  obtain ⟨p, hp⟩ := hzero
  obtain ⟨u, humem, hune, huim, hulim, htlim⟩ := exists_verticalApproach hε hS
  have htne : ∀ j, u j - ζ ≠ 0 := fun j => sub_ne_zero.mpr (hune j)
  have hzeroim : (ζ + σ k₀).im = 0 := by
    rw [hp]
    simp
  have hupper : ∀ j, 0 < (u j + σ k₀).im := by
    intro j
    have h1 : (u j + σ k₀).im = (u j - ζ).im + (ζ + σ k₀).im := by
      simp only [Complex.add_im, Complex.sub_im]
      ring
    rw [h1, hzeroim, add_zero]
    exact huim j
  have hgroup : ∀ k, σ k = σ k₀ → ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun j => iteratedDeriv (m k) C.carrier (u j + σ k) *
        (u j - ζ) ^ ((m k : ℤ) + 1)) atTop (𝓝 c) := by
    intro k hk
    have hupperk : ∀ j, 0 < (u j + σ k).im := by
      intro j
      rw [hk]
      exact hupper j
    have hlim' : Tendsto u atTop (𝓝 ((C.pole p : ℂ) - σ k)) := by
      rw [hk, ← hp]
      exact hulim
    obtain ⟨c, hcne, hc⟩ := C.jetBlowUp p (m k) (σ k) u hupperk hlim'
    refine ⟨c, hcne, hc.congr fun j => ?_⟩
    rw [show ((m k : ℤ) + 1) = ((m k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, hp, hk]
  have hcomp : ∀ k, σ k ≠ σ k₀ → ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun j => iteratedDeriv (m k) C.carrier (u j + σ k) *
        (u j - ζ) ^ (-(V k : ℤ))) atTop (𝓝 c) :=
    fun k hk => exists_tendsto_zpow_neg_of_analyticOrderAt (hfin k hk) (hV k hk) hulim hune
  refine ⟨u, fun j => u j - ζ,
    fun k => if hk : σ k = σ k₀ then (hgroup k hk).choose else (hcomp k hk).choose,
    humem, htne, hulim, htlim, ?_, ?_⟩
  · intro k
    dsimp only
    by_cases hk : σ k = σ k₀
    · rw [dif_pos hk]
      exact (hgroup k hk).choose_spec.1
    · rw [dif_neg hk]
      exact (hcomp k hk).choose_spec.1
  · intro k
    dsimp only
    by_cases hk : σ k = σ k₀
    · rw [dif_pos hk]
      have hrate : integerTranslateJetGroupRate m σ k₀ V k = (m k : ℤ) + 1 := by
        rw [integerTranslateJetGroupRate, if_pos hk]
      rw [hrate]
      exact (hgroup k hk).choose_spec.2
    · rw [dif_neg hk]
      have hrate : integerTranslateJetGroupRate m σ k₀ V k = -(V k : ℤ) := by
        rw [integerTranslateJetGroupRate, if_neg hk]
      rw [hrate]
      exact (hcomp k hk).choose_spec.2

/-- **Point-dependent group blow-up data for an arbitrary pole carrier.** -/
theorem pointwiseData {κ : Type*} {n : ℕ} (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n)
    (V : ℂ → Fin n → ℕ) {S Z : Set ℂ} {ε : ℝ} (hε : 0 < ε) (exponent : κ → (Fin n →₀ ℕ))
    (hZ : Z.Infinite)
    (hS : ∀ ζ ∈ Z, ∀ y : ℝ, 0 < y → y < ε → ζ + (y : ℂ) * Complex.I ∈ S)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (C.pole p : ℂ) - σ k₀)
    (hfin : ∀ ζ ∈ Z, ∀ k, σ k ≠ σ k₀ →
      AnalyticAt ℂ (fun w => iteratedDeriv (m k) C.carrier (w + σ k)) ζ)
    (hV : ∀ ζ ∈ Z, ∀ k, σ k ≠ σ k₀ →
      analyticOrderAt (fun w => iteratedDeriv (m k) C.carrier (w + σ k)) ζ = ((V ζ k : ℕ) : ℕ∞))
    (hsep : ∀ ζ ∈ Z, Function.Injective fun a =>
      integerBlowUpOrder (integerTranslateJetGroupRate m σ k₀ (V ζ)) (exponent a)) :
    PointwiseIntegerMultiBlowUpData S
      (fun k w => iteratedDeriv (m k) C.carrier (w + σ k)) Z exponent := by
  refine ⟨hZ, fun ζ hζ => ?_⟩
  obtain ⟨u, t, c, humem, htne, hu, ht, hcne, hlim⟩ :=
    C.exists_groupBlowUp_at m σ k₀ (V ζ) hε (hS ζ hζ) (hzero ζ hζ) (hfin ζ hζ) (hV ζ hζ)
  exact ⟨u, t, c, integerTranslateJetGroupRate m σ k₀ (V ζ),
    humem, htne, hu, ht, hcne, hsep ζ hζ, hlim⟩

set_option maxHeartbeats 1000000 in
/-- **Full-rank node packets in a prescribed sampled set, for an arbitrary pole carrier.** -/
theorem exists_row_packet_in_set
    {κ row : Type*} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Fintype row] {n q : ℕ}
    (m : Fin n → ℕ) (σ : Fin n → ℂ) (k₀ : Fin n)
    (exponent : κ → (Fin n →₀ ℕ)) {S Z : Set ℂ} {ε : ℝ} (hε : 0 < ε)
    (hSinf : S.Infinite) (hZ : Z.Infinite)
    (hS : ∀ ζ ∈ Z, ∀ y : ℝ, 0 < y → y < ε → ζ + (y : ℂ) * Complex.I ∈ S)
    (hzero : ∀ ζ ∈ Z, ∃ p : ℕ, ζ = (C.pole p : ℂ) - σ k₀)
    (hshift : ∀ k, σ k ≠ σ k₀ → (σ k₀).im < (σ k).im)
    (hmono : ∀ k, σ k = σ k₀ → Monotone fun a => exponent a k)
    (hanti : ∀ k, σ k ≠ σ k₀ → Antitone fun a => exponent a k)
    (hstrict : StrictMono fun a => exponent a k₀)
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, (∀ b, z b ∈ S) ∧ Function.Injective z ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q n z exponent
        (fun p => iteratedDeriv (m p.2) C.carrier (z p.1 + σ p.2))).mulVec := by
  classical
  have him : ∀ ζ ∈ Z, ζ.im = -(σ k₀).im := by
    intro ζ hζ
    obtain ⟨p, rfl⟩ := hzero ζ hζ
    simp
  refine exists_row_packet_of_linearIndependent_box (q := q) hSinf
    (fun k w => iteratedDeriv (m k) C.carrier (w + σ k)) exponent ?_ f hf
  refine linearIndependent_restrict_expandedMonomialFamily_of_pointwiseIntegerMultiBlowUp
    (κ := κ) (q := q) (S := S) (Z := Z) (exponent := exponent) ?_
  refine C.pointwiseData m σ k₀ (fun ζ k => C.jetOrder (m k) (σ k) ζ) hε exponent hZ hS hzero
    ?_ ?_ ?_
  · intro ζ hζ k hk
    refine C.analyticJet (m k) (σ k) ζ ?_
    have h1 : (ζ + σ k).im = ζ.im + (σ k).im := by simp
    rw [h1, him ζ hζ]
    have := hshift k hk
    linarith
  · intro ζ hζ k hk
    refine C.analyticOrderAt_jet_eq (m k) ?_
    rw [him ζ hζ]
    have := hshift k hk
    linarith
  · intro ζ _
    exact injective_integerBlowUpOrder_of_signed_box _ exponent (fun k => σ k = σ k₀) k₀
      (fun k hk => (integerTranslateJetGroupRate_pos m σ k₀ _ hk).le)
      (fun k hk => integerTranslateJetGroupRate_nonpos m σ k₀ _ hk)
      hmono hanti (integerTranslateJetGroupRate_pos m σ k₀ _ rfl) hstrict

/-! ## Spaced rays -/

/-- Two poles whose indices are `K`-spaced are separated by more than `K − 1/2`. -/
theorem spacedPole_gap (K : ℕ) {a b : ℕ} (hab : a < b) :
    (K : ℝ) - 1 / 2 < C.pole (b * K) - C.pole (a * K) := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp only [Nat.mul_zero, Nat.cast_zero]
    norm_num
  · have hstep : a * K + K ≤ b * K := by
      calc a * K + K = (a + 1) * K := by ring
        _ ≤ b * K := Nat.mul_le_mul_right K hab
    have hlt : a * K < b * K := by
      have : 0 < K := hK
      omega
    have hgap := C.gap (a * K) (b * K) hlt
    have hcast : ((a * K : ℕ) : ℝ) + (K : ℝ) ≤ ((b * K : ℕ) : ℝ) := by exact_mod_cast hstep
    linarith

/-- Nodes on truncated vertical rays over a `K`-spaced subsequence of the poles. -/
noncomputable def spacedRayNodes (σ₀ : ℂ) (K : ℕ) (ε : ℝ) : Set ℂ :=
  {w | ∃ (j : ℕ) (y : ℝ), 0 < y ∧ y < ε ∧ w = ((C.pole (j * K) : ℂ) - σ₀) + (y : ℂ) * Complex.I}

/-- The base points of the sampled rays. -/
noncomputable def spacedRayBase (σ₀ : ℂ) (K : ℕ) : Set ℂ :=
  Set.range fun j : ℕ => ((C.pole (j * K) : ℂ) - σ₀)

theorem injective_spacedRayBase (σ₀ : ℂ) {K : ℕ} (hK : 0 < K) :
    Function.Injective fun j : ℕ => ((C.pole (j * K) : ℂ) - σ₀) := by
  intro j₁ j₂ hj
  have hre : C.pole (j₁ * K) - σ₀.re = C.pole (j₂ * K) - σ₀.re := by
    simpa using congrArg Complex.re hj
  have hz : C.pole (j₁ * K) = C.pole (j₂ * K) := by linarith
  exact Nat.eq_of_mul_eq_mul_right hK (C.pole_injective hz)

theorem infinite_spacedRayBase (σ₀ : ℂ) {K : ℕ} (hK : 0 < K) :
    (C.spacedRayBase σ₀ K).Infinite :=
  Set.infinite_range_of_injective (C.injective_spacedRayBase σ₀ hK)

theorem infinite_spacedRayNodes (σ₀ : ℂ) {K : ℕ} {ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    (C.spacedRayNodes σ₀ K ε).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ => ((C.pole (j * K) : ℂ) - σ₀) + ((ε / 2 : ℝ) : ℂ) * Complex.I) ?_ ?_
  · intro j₁ j₂ hj
    refine C.injective_spacedRayBase σ₀ hK ?_
    have := congrArg (fun w : ℂ => w - ((ε / 2 : ℝ) : ℂ) * Complex.I) hj
    simpa using this
  · intro j
    exact ⟨j, ε / 2, by linarith, by linarith, rfl⟩

theorem spacedRayNodes_mem_of_base (σ₀ : ℂ) (K : ℕ) {ε : ℝ} {ζ : ℂ}
    (hζ : ζ ∈ C.spacedRayBase σ₀ K) :
    ∀ y : ℝ, 0 < y → y < ε → ζ + (y : ℂ) * Complex.I ∈ C.spacedRayNodes σ₀ K ε := by
  obtain ⟨j, rfl⟩ := hζ
  exact fun y hy hyε => ⟨j, y, hy, hyε, rfl⟩

theorem spacedRayNodes_im_lt {σ₀ : ℂ} {K : ℕ} {ε : ℝ} {w : ℂ}
    (hw : w ∈ C.spacedRayNodes σ₀ K ε) : -σ₀.im < w.im := by
  obtain ⟨j, y, hy0, _, rfl⟩ := hw
  simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
  linarith

set_option maxHeartbeats 800000 in
/-- **The separation dichotomy.**  Two distinct sampled nodes are either closer than the truncation
height or farther apart than the spacing: the middle band is empty. -/
theorem spacedRayNodes_dichotomy (σ₀ : ℂ) {K : ℕ} {ε : ℝ} (hK : 0 < K)
    {w w' : ℂ} (hw : w ∈ C.spacedRayNodes σ₀ K ε) (hw' : w' ∈ C.spacedRayNodes σ₀ K ε)
    (hne : w ≠ w') : ‖w - w'‖ < ε ∨ (K : ℝ) - 1 / 2 < ‖w - w'‖ := by
  obtain ⟨j, y, hy0, hyε, rfl⟩ := hw
  obtain ⟨j', y', hy0', hyε', rfl⟩ := hw'
  by_cases hj : j = j'
  · subst hj
    left
    have hdiff : ((C.pole (j * K) : ℂ) - σ₀) + (y : ℂ) * Complex.I
        - (((C.pole (j * K) : ℂ) - σ₀) + (y' : ℂ) * Complex.I)
        = (((y - y' : ℝ)) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hdiff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  · right
    have hre : (((C.pole (j * K) : ℂ) - σ₀) + (y : ℂ) * Complex.I
        - (((C.pole (j' * K) : ℂ) - σ₀) + (y' : ℂ) * Complex.I)).re
        = C.pole (j * K) - C.pole (j' * K) := by
      simp
    have habs : (K : ℝ) - 1 / 2 < |C.pole (j * K) - C.pole (j' * K)| := by
      have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      rcases lt_or_gt_of_ne hj with h | h
      · have hgap := C.spacedPole_gap K h
        rw [abs_sub_comm, abs_of_pos (by linarith)]
        exact hgap
      · have hgap := C.spacedPole_gap K h
        rw [abs_of_pos (by linarith)]
        exact hgap
    calc (K : ℝ) - 1 / 2 < |C.pole (j * K) - C.pole (j' * K)| := habs
      _ = |(((C.pole (j * K) : ℂ) - σ₀) + (y : ℂ) * Complex.I
            - (((C.pole (j' * K) : ℂ) - σ₀) + (y' : ℂ) * Complex.I)).re| := by rw [hre]
      _ ≤ _ := Complex.abs_re_le_norm _

/-- **The collision-free connector.**  Nodes drawn from the sampled rays make the whole row-by-shift
family injective, provided every nonzero shift difference has modulus between the truncation height
and the spacing. -/
theorem injective_combined_of_spacedRayNodes {row ι : Type*} (σ₀ : ℂ) {K : ℕ} {ε : ℝ} (hK : 0 < K)
    (z : row → ℂ) (hzmem : ∀ b, z b ∈ C.spacedRayNodes σ₀ K ε) (hzinj : Function.Injective z)
    (shift : ι → ℂ) (hshiftinj : Function.Injective shift)
    (hlow : ∀ i i' : ι, i ≠ i' → ε ≤ ‖shift i - shift i'‖)
    (hhigh : ∀ i i' : ι, ‖shift i - shift i'‖ ≤ (K : ℝ) - 1 / 2) :
    Function.Injective fun x : row × ι => z x.1 + shift x.2 := by
  rintro ⟨r, i⟩ ⟨r', i'⟩ h
  dsimp only at h
  by_cases hr : r = r'
  · subst hr
    have hs : shift i = shift i' := by linear_combination h
    exact Prod.ext rfl (hshiftinj hs)
  · exfalso
    have hzne : z r ≠ z r' := fun hc => hr (hzinj hc)
    have hii : i ≠ i' := by
      intro hc
      subst hc
      exact hzne (by linear_combination h)
    have hdiff : z r - z r' = shift i' - shift i := by linear_combination h
    have hnorm : ‖z r - z r'‖ = ‖shift i' - shift i‖ := by rw [hdiff]
    rcases C.spacedRayNodes_dichotomy σ₀ hK (hzmem r) (hzmem r') hzne with hlt | hgt
    · rw [hnorm] at hlt
      have := hlow i' i (Ne.symm hii)
      linarith
    · rw [hnorm] at hgt
      have := hhigh i' i
      linarith

end PoleCarrier

/-! ## The moving canonical instance -/

/-- The moving canonical logarithmic derivative, as a pole carrier. -/
noncomputable def movingCanonicalPoleCarrier (θ : BoundedRealSequence) : PoleCarrier where
  carrier := movingCanonicalLogDerivative θ
  pole := movingCanonicalZero θ
  gap := by
    intro a b _
    have h1 := movingCanonicalZero_lower θ b
    have h2 := movingCanonicalZero_upper θ a
    linarith
  analyticJet := fun r σ _ h => analyticAt_translate_jet r σ h
  jetBlowUp := fun p r σ _ hupper hu =>
    ⟨-((-1 : ℂ) ^ r * (r.factorial : ℂ)), jetLeadingValue_ne_zero r,
      tendsto_iteratedDeriv_translate_movingCanonicalLogDerivative θ p r σ hupper hu⟩

@[simp] theorem movingCanonicalPoleCarrier_carrier (θ : BoundedRealSequence) :
    (movingCanonicalPoleCarrier θ).carrier = movingCanonicalLogDerivative θ := rfl

@[simp] theorem movingCanonicalPoleCarrier_pole (θ : BoundedRealSequence) :
    (movingCanonicalPoleCarrier θ).pole = movingCanonicalZero θ := rfl

end GaloisForLFunctions.HTGeometry
