/-
The arc-winding dictionary: the deck cocycle in logarithm coordinates, and the
anchor's monodromy-free contribution.

The finite Euler head has a GLOBAL canonical logarithm on the right half-plane:
each factor `1 − p^{−s}` stays in the open right half-plane, hence in the slit
plane, so the principal factor logarithms sum to an analytic branch whose
imaginary part is exactly the anchor tilt.  Consequently the anchor contributes no
monodromy to any arc — the imaginary increment of ANY continuous logarithm of the
anchor along ANY path in the right half-plane is the difference of the endpoint
tilts — and every logarithm of the anchored member splits its arc winding as
member increment plus endpoint tilt difference.

The deck cocycle reads off in the same coordinates: for any chart logarithms
`ℓ₁, ℓ₂` of the member on the two overlap charts, the square-root deck class value at
the two basepoints is `exp` of half the log mismatch `(ℓ₁ − ℓ₂)(pP) − (ℓ₁ − ℓ₂)(pM)`,
and since each pointwise mismatch is `2πi`-quantized the class is `(−1)^{k_P − k_M}`:
the parity of the winding mismatch between the two basepoints.  Local root choices
cancel in the double ratio.  So the parity datum is a difference of arc-winding
integers, the anchor moves it only through the endpoint tilt pair — dense by
pair-reachability — and the member's hole winding is pinned by the zero count.
-/
import GaloisForLFunctions.RHTower.EndpointNoGo
import GaloisForLFunctions.RHTower.ArgumentVariation

noncomputable section

namespace RHTower

open Complex Metric Finset

/-! ### §1 The canonical anchor logarithm -/

/-- The canonical logarithm of the finite Euler head: the sum of the principal
logarithms of the factors. -/
noncomputable def anchorLog (P : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ P, Complex.log (1 - (p : ℂ) ^ (-s))

/-- Each Euler factor lies in the slit plane on the right half-plane. -/
theorem eulerFactor_mem_slitPlane {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    (1 - (p : ℂ) ^ (-s)) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (re_eulerFactor_pos hp hs))

/-- Finite sums of analytic functions are analytic. -/
theorem analyticAt_finset_sum {ι : Type*} (P : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (h : ∀ p ∈ P, AnalyticAt ℂ (f p) z) :
    AnalyticAt ℂ (fun s => ∑ p ∈ P, f p s) z := by
  classical
  induction P using Finset.induction_on with
  | empty => simpa using analyticAt_const
  | insert a s ha ih =>
      rw [show (fun w => ∑ p ∈ insert a s, f p w)
          = fun w => f a w + ∑ p ∈ s, f p w from by
        funext w; rw [Finset.sum_insert ha]]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun p hp => h p (Finset.mem_insert_of_mem hp))

/-- The canonical anchor logarithm is analytic on the right half-plane. -/
theorem anchorLog_analyticAt {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {s : ℂ}
    (hs : 0 < s.re) :
    AnalyticAt ℂ (anchorLog P) s := by
  apply analyticAt_finset_sum
  intro p hp
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hP p hp; omega)
  have hfac : AnalyticAt ℂ (fun w : ℂ => 1 - (p : ℂ) ^ (-w)) s := by
    have hd : Differentiable ℂ (fun w : ℂ => 1 - (p : ℂ) ^ (-w)) := fun w =>
      (differentiableAt_const (1 : ℂ)).sub
        (differentiableAt_id.neg.const_cpow (Or.inl hp0))
    exact (hd.differentiableOn.analyticOnNhd isOpen_univ) s (Set.mem_univ s)
  exact hfac.clog (eulerFactor_mem_slitPlane (hP p hp) hs)

/-- The canonical anchor logarithm exponentiates to the anchor. -/
theorem exp_anchorLog {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {s : ℂ}
    (hs : 0 < s.re) :
    Complex.exp (anchorLog P s) = eulerHeadAnchor P s := by
  rw [anchorLog, Complex.exp_sum, eulerHeadAnchor]
  refine Finset.prod_congr rfl fun p hp => ?_
  refine Complex.exp_log ?_
  intro h0
  have hre := re_eulerFactor_pos (hP p hp) hs
  rw [h0] at hre
  simp at hre

/-- The imaginary part of the canonical anchor logarithm is the anchor tilt. -/
theorem anchorLog_im (P : Finset ℕ) (s : ℂ) :
    (anchorLog P s).im = anchorTilt P s := by
  rw [anchorLog, Complex.im_sum, anchorTilt]
  exact Finset.sum_congr rfl fun p _ => Complex.log_im _

/-! ### §2 The anchor never winds: arc variation is the endpoint tilt difference -/

/-- **The anchor carries no monodromy**: along any continuous path in the right
half-plane, the imaginary increment of ANY continuous logarithm of the anchor is
the difference of the endpoint anchor tilts.  The anchor's argument variation is
an exact endpoint datum. -/
theorem anchor_arc_variation {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b))
    (hre : ∀ t ∈ Set.Icc a b, 0 < (γ t).re)
    {ℓ : ℝ → ℂ} (hℓ : ContinuousOn ℓ (Set.Icc a b))
    (hexp : ∀ t ∈ Set.Icc a b, Complex.exp (ℓ t) = eulerHeadAnchor P (γ t)) :
    (ℓ b).im - (ℓ a).im = anchorTilt P (γ b) - anchorTilt P (γ a) := by
  have hAcont : ContinuousOn (fun t => anchorLog P (γ t)) (Set.Icc a b) :=
    fun t ht => ((anchorLog_analyticAt hP (hre t ht)).continuousAt).comp_continuousWithinAt
      (hγ t ht)
  have hFcont : ContinuousOn (fun t => (ℓ t).im - (anchorLog P (γ t)).im)
      (Set.Icc a b) :=
    (Complex.continuous_im.comp_continuousOn hℓ).sub
      (Complex.continuous_im.comp_continuousOn hAcont)
  have hint : ∀ τ ∈ Set.Icc a b,
      ∃ n : ℤ, (ℓ τ).im - (anchorLog P (γ τ)).im = n * (2 * Real.pi) := by
    intro τ hτ
    have hAne : eulerHeadAnchor P (γ τ) ≠ 0 :=
      eulerHeadAnchor_ne_zero hP (hre τ hτ)
    have h1 : Complex.exp (ℓ τ - anchorLog P (γ τ)) = 1 := by
      rw [Complex.exp_sub, hexp τ hτ, exp_anchorLog hP (hre τ hτ), div_self hAne]
    obtain ⟨n, hn⟩ := im_eq_int_mul_two_pi_of_exp_pos (r := 1) one_pos
      (by rw [h1]; norm_num)
    refine ⟨n, ?_⟩
    rw [← Complex.sub_im]
    exact hn
  have hconst := continuousOn_int_mul_two_pi_const hab hFcont hint b
    (Set.right_mem_Icc.mpr hab)
  have hconst' : (ℓ b).im - (anchorLog P (γ b)).im
      = (ℓ a).im - (anchorLog P (γ a)).im := hconst
  have hb' := anchorLog_im P (γ b)
  have ha' := anchorLog_im P (γ a)
  linarith

/-- **The arc-winding dictionary for the anchored member**: along any path in the
right half-plane, any continuous logarithm of the anchored member splits its
imaginary increment as the member logarithm's increment plus the endpoint tilt
difference.  The member's increment around the hole is pinned by the zero count;
the tilt difference is the pair-reachable steering datum. -/
theorem anchoredSEM_arc_variation {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {N : ℕ}
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b))
    (hre : ∀ t ∈ Set.Icc a b, 0 < (γ t).re)
    {ℓ m : ℝ → ℂ} (hℓ : ContinuousOn ℓ (Set.Icc a b))
    (hm : ContinuousOn m (Set.Icc a b))
    (hexpℓ : ∀ t ∈ Set.Icc a b, Complex.exp (ℓ t) = anchoredSEM P N (γ t))
    (hexpm : ∀ t ∈ Set.Icc a b, Complex.exp (m t) = completedSEM N (γ t)) :
    (ℓ b).im - (ℓ a).im
      = ((m b).im - (m a).im) + (anchorTilt P (γ b) - anchorTilt P (γ a)) := by
  have h := anchor_arc_variation hP hab hγ hre (ℓ := fun t => ℓ t - m t)
    (hℓ.sub hm) (fun t ht => by
      have hG : completedSEM N (γ t) ≠ 0 := by
        rw [← hexpm t ht]
        exact Complex.exp_ne_zero _
      rw [Complex.exp_sub, hexpℓ t ht, hexpm t ht,
        show anchoredSEM P N (γ t)
          = eulerHeadAnchor P (γ t) * completedSEM N (γ t) from rfl,
        mul_div_assoc, div_self hG, mul_one])
  simp only [Complex.sub_im] at h
  linarith

/-! ### §3 The deck cocycle in logarithm coordinates -/

/-- **The deck cocycle from chart logarithms**: for any chart logarithms
`ℓ₁, ℓ₂` of the same function on the two overlap charts and any analytic square
roots `G₁, G₂` there, the deck class value at the two basepoints is `exp` of half the
log mismatch between the basepoints — the local root choices cancel in the double
ratio. -/
theorem deckClass_eq_exp_log_mismatch {f G₁ G₂ ℓ₁ ℓ₂ : ℂ → ℂ} {U₁ U₂ : Set ℂ}
    (hU₁ : IsOpen U₁) (hU₁c : IsPreconnected U₁)
    (hU₂ : IsOpen U₂) (hU₂c : IsPreconnected U₂)
    (hG₁ : AnalyticOnNhd ℂ G₁ U₁) (hG₂ : AnalyticOnNhd ℂ G₂ U₂)
    (hpG₁ : ∀ z ∈ U₁, G₁ z ^ 2 = f z) (hpG₂ : ∀ z ∈ U₂, G₂ z ^ 2 = f z)
    (hℓ₁ : AnalyticOnNhd ℂ ℓ₁ U₁) (hℓ₂ : AnalyticOnNhd ℂ ℓ₂ U₂)
    (hexp₁ : ∀ z ∈ U₁, Complex.exp (ℓ₁ z) = f z)
    (hexp₂ : ∀ z ∈ U₂, Complex.exp (ℓ₂ z) = f z)
    {pP pM : ℂ} (hpP₁ : pP ∈ U₁) (hpP₂ : pP ∈ U₂)
    (hpM₁ : pM ∈ U₁) (hpM₂ : pM ∈ U₂) :
    deckClass G₁ G₂ pP pM
      = Complex.exp ((ℓ₁ pP - ℓ₂ pP - (ℓ₁ pM - ℓ₂ pM)) / 2) := by
  have hfP : f pP ≠ 0 := by
    rw [← hexp₁ pP hpP₁]
    exact Complex.exp_ne_zero _
  have hE₁ : AnalyticOnNhd ℂ (fun z => Complex.exp (ℓ₁ z / 2)) U₁ := fun z hz =>
    ((hℓ₁ z hz).div analyticAt_const (by norm_num)).cexp
  have hE₂ : AnalyticOnNhd ℂ (fun z => Complex.exp (ℓ₂ z / 2)) U₂ := fun z hz =>
    ((hℓ₂ z hz).div analyticAt_const (by norm_num)).cexp
  have hpE₁ : ∀ z ∈ U₁, Complex.exp (ℓ₁ z / 2) ^ 2 = f z := fun z hz => by
    rw [sq, ← Complex.exp_add, show ℓ₁ z / 2 + ℓ₁ z / 2 = ℓ₁ z from by ring]
    exact hexp₁ z hz
  have hpE₂ : ∀ z ∈ U₂, Complex.exp (ℓ₂ z / 2) ^ 2 = f z := fun z hz => by
    rw [sq, ← Complex.exp_add, show ℓ₂ z / 2 + ℓ₂ z / 2 = ℓ₂ z from by ring]
    exact hexp₂ z hz
  obtain ⟨hc₁sq, hEq₁⟩ := pow_root_ratio (by norm_num : (0 : ℕ) < 2) hU₁ hU₁c
    hG₁ hE₁ hpG₁ hpE₁ hpP₁ hfP
  obtain ⟨hc₂sq, hEq₂⟩ := pow_root_ratio (by norm_num : (0 : ℕ) < 2) hU₂ hU₂c
    hG₂ hE₂ hpG₂ hpE₂ hpP₂ hfP
  set c₁ : ℂ := G₁ pP / Complex.exp (ℓ₁ pP / 2) with hc₁def
  set c₂ : ℂ := G₂ pP / Complex.exp (ℓ₂ pP / 2) with hc₂def
  have hc₁ : c₁ ≠ 0 := by
    intro h
    rw [h] at hc₁sq
    norm_num at hc₁sq
  have hc₂ : c₂ ≠ 0 := by
    intro h
    rw [h] at hc₂sq
    norm_num at hc₂sq
  have e1P : G₁ pP = c₁ * Complex.exp (ℓ₁ pP / 2) := hEq₁ hpP₁
  have e2P : G₂ pP = c₂ * Complex.exp (ℓ₂ pP / 2) := hEq₂ hpP₂
  have e1M : G₁ pM = c₁ * Complex.exp (ℓ₁ pM / 2) := hEq₁ hpM₁
  have e2M : G₂ pM = c₂ * Complex.exp (ℓ₂ pM / 2) := hEq₂ hpM₂
  have hE : Complex.exp ((ℓ₁ pP - ℓ₂ pP - (ℓ₁ pM - ℓ₂ pM)) / 2)
      = Complex.exp (ℓ₁ pP / 2) / Complex.exp (ℓ₂ pP / 2)
        / (Complex.exp (ℓ₁ pM / 2) / Complex.exp (ℓ₂ pM / 2)) := by
    rw [show (ℓ₁ pP - ℓ₂ pP - (ℓ₁ pM - ℓ₂ pM)) / 2
        = ℓ₁ pP / 2 - ℓ₂ pP / 2 - (ℓ₁ pM / 2 - ℓ₂ pM / 2) from by ring,
      Complex.exp_sub, Complex.exp_sub, Complex.exp_sub]
  rw [deckClass, e1P, e2P, e1M, e2M, hE]
  have h1 := Complex.exp_ne_zero (ℓ₁ pP / 2)
  have h2 := Complex.exp_ne_zero (ℓ₂ pP / 2)
  have h3 := Complex.exp_ne_zero (ℓ₁ pM / 2)
  have h4 := Complex.exp_ne_zero (ℓ₂ pM / 2)
  field_simp

/-- **The deck cocycle is the parity of the winding mismatch**: the pointwise
mismatch of two chart logarithms is `2πi`-quantized, and the square-root deck
value at the two basepoints is `(−1)` to the difference of the two quantization
integers.  The parity datum is a difference of arc-winding integers — not the
endpoint orientation signs. -/
theorem deckClass_neg_one_zpow_log_mismatch {f G₁ G₂ ℓ₁ ℓ₂ : ℂ → ℂ} {U₁ U₂ : Set ℂ}
    (hU₁ : IsOpen U₁) (hU₁c : IsPreconnected U₁)
    (hU₂ : IsOpen U₂) (hU₂c : IsPreconnected U₂)
    (hG₁ : AnalyticOnNhd ℂ G₁ U₁) (hG₂ : AnalyticOnNhd ℂ G₂ U₂)
    (hpG₁ : ∀ z ∈ U₁, G₁ z ^ 2 = f z) (hpG₂ : ∀ z ∈ U₂, G₂ z ^ 2 = f z)
    (hℓ₁ : AnalyticOnNhd ℂ ℓ₁ U₁) (hℓ₂ : AnalyticOnNhd ℂ ℓ₂ U₂)
    (hexp₁ : ∀ z ∈ U₁, Complex.exp (ℓ₁ z) = f z)
    (hexp₂ : ∀ z ∈ U₂, Complex.exp (ℓ₂ z) = f z)
    {pP pM : ℂ} (hpP₁ : pP ∈ U₁) (hpP₂ : pP ∈ U₂)
    (hpM₁ : pM ∈ U₁) (hpM₂ : pM ∈ U₂) :
    ∃ kP kM : ℤ,
      ℓ₁ pP - ℓ₂ pP = kP * (2 * Real.pi * I) ∧
      ℓ₁ pM - ℓ₂ pM = kM * (2 * Real.pi * I) ∧
      deckClass G₁ G₂ pP pM = (-1 : ℂ) ^ (kP - kM) := by
  have hfP : f pP ≠ 0 := by
    rw [← hexp₁ pP hpP₁]
    exact Complex.exp_ne_zero _
  have hfM : f pM ≠ 0 := by
    rw [← hexp₁ pM hpM₁]
    exact Complex.exp_ne_zero _
  obtain ⟨kP, hkP⟩ : ∃ n : ℤ, ℓ₁ pP - ℓ₂ pP = n * (2 * Real.pi * I) := by
    apply Complex.exp_eq_one_iff.mp
    rw [Complex.exp_sub, hexp₁ pP hpP₁, hexp₂ pP hpP₂, div_self hfP]
  obtain ⟨kM, hkM⟩ : ∃ n : ℤ, ℓ₁ pM - ℓ₂ pM = n * (2 * Real.pi * I) := by
    apply Complex.exp_eq_one_iff.mp
    rw [Complex.exp_sub, hexp₁ pM hpM₁, hexp₂ pM hpM₂, div_self hfM]
  refine ⟨kP, kM, hkP, hkM, ?_⟩
  rw [deckClass_eq_exp_log_mismatch hU₁ hU₁c hU₂ hU₂c hG₁ hG₂ hpG₁ hpG₂
    hℓ₁ hℓ₂ hexp₁ hexp₂ hpP₁ hpP₂ hpM₁ hpM₂, hkP, hkM,
    show ((kP : ℂ) * (2 * (Real.pi : ℂ) * I) - (kM : ℂ) * (2 * (Real.pi : ℂ) * I)) / 2
      = ((kP - kM : ℤ) : ℂ) * ((Real.pi : ℂ) * I) from by push_cast; ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- **The deck cocycle from boundary-arc argument variations**: the class is `(−1)^k`
where `2πk` is the difference between the argument variation of the member along the
first chart (from `pM` to `pP`) and along the second — the two-arc winding mismatch. -/
theorem deckClass_neg_one_zpow_arg_variation {f G₁ G₂ ℓ₁ ℓ₂ : ℂ → ℂ} {U₁ U₂ : Set ℂ}
    (hU₁ : IsOpen U₁) (hU₁c : IsPreconnected U₁)
    (hU₂ : IsOpen U₂) (hU₂c : IsPreconnected U₂)
    (hG₁ : AnalyticOnNhd ℂ G₁ U₁) (hG₂ : AnalyticOnNhd ℂ G₂ U₂)
    (hpG₁ : ∀ z ∈ U₁, G₁ z ^ 2 = f z) (hpG₂ : ∀ z ∈ U₂, G₂ z ^ 2 = f z)
    (hℓ₁ : AnalyticOnNhd ℂ ℓ₁ U₁) (hℓ₂ : AnalyticOnNhd ℂ ℓ₂ U₂)
    (hexp₁ : ∀ z ∈ U₁, Complex.exp (ℓ₁ z) = f z)
    (hexp₂ : ∀ z ∈ U₂, Complex.exp (ℓ₂ z) = f z)
    {pP pM : ℂ} (hpP₁ : pP ∈ U₁) (hpP₂ : pP ∈ U₂)
    (hpM₁ : pM ∈ U₁) (hpM₂ : pM ∈ U₂) :
    ∃ k : ℤ,
      ((ℓ₁ pP).im - (ℓ₁ pM).im) - ((ℓ₂ pP).im - (ℓ₂ pM).im) = k * (2 * Real.pi) ∧
      deckClass G₁ G₂ pP pM = (-1 : ℂ) ^ k := by
  obtain ⟨kP, kM, hkP, hkM, hdc⟩ := deckClass_neg_one_zpow_log_mismatch hU₁ hU₁c
    hU₂ hU₂c hG₁ hG₂ hpG₁ hpG₂ hℓ₁ hℓ₂ hexp₁ hexp₂ hpP₁ hpP₂ hpM₁ hpM₂
  refine ⟨kP - kM, ?_, hdc⟩
  have hP := congrArg Complex.im hkP
  have hM := congrArg Complex.im hkM
  simp only [Complex.sub_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat] at hP hM
  push_cast
  linarith

/-- **Rigidity from monodromy-freeness**: adding the canonical anchor logarithm to
both chart logarithms produces chart logarithms of the ANCHORED member with the SAME
pointwise mismatches — the anchor's contribution is endpoint-pure and identical on
both charts, so it cancels from the winding mismatch entirely.  The anchored deck
class equals the member's `(−1)^k` with the member's own `k`: the prime set cannot
move the parity through the winding integers of any fixed chart logarithms, only
through the branch the gluing selects. -/
theorem anchoredSEM_deckClass_neg_one_zpow_arg_variation {P : Finset ℕ}
    (hP : ∀ p ∈ P, 2 ≤ p) {N : ℕ} {G₁ G₂ ℓ₁ ℓ₂ : ℂ → ℂ} {U₁ U₂ : Set ℂ}
    (hU₁ : IsOpen U₁) (hU₁c : IsPreconnected U₁)
    (hU₂ : IsOpen U₂) (hU₂c : IsPreconnected U₂)
    (hre₁ : ∀ z ∈ U₁, 0 < z.re) (hre₂ : ∀ z ∈ U₂, 0 < z.re)
    (hG₁ : AnalyticOnNhd ℂ G₁ U₁) (hG₂ : AnalyticOnNhd ℂ G₂ U₂)
    (hpG₁ : ∀ z ∈ U₁, G₁ z ^ 2 = anchoredSEM P N z)
    (hpG₂ : ∀ z ∈ U₂, G₂ z ^ 2 = anchoredSEM P N z)
    (hℓ₁ : AnalyticOnNhd ℂ ℓ₁ U₁) (hℓ₂ : AnalyticOnNhd ℂ ℓ₂ U₂)
    (hexp₁ : ∀ z ∈ U₁, Complex.exp (ℓ₁ z) = completedSEM N z)
    (hexp₂ : ∀ z ∈ U₂, Complex.exp (ℓ₂ z) = completedSEM N z)
    {pP pM : ℂ} (hpP₁ : pP ∈ U₁) (hpP₂ : pP ∈ U₂)
    (hpM₁ : pM ∈ U₁) (hpM₂ : pM ∈ U₂) :
    ∃ k : ℤ,
      ((ℓ₁ pP).im - (ℓ₁ pM).im) - ((ℓ₂ pP).im - (ℓ₂ pM).im) = k * (2 * Real.pi) ∧
      deckClass G₁ G₂ pP pM = (-1 : ℂ) ^ k := by
  have hL₁ : AnalyticOnNhd ℂ (fun z => ℓ₁ z + anchorLog P z) U₁ := fun z hz =>
    (hℓ₁ z hz).add (anchorLog_analyticAt hP (hre₁ z hz))
  have hL₂ : AnalyticOnNhd ℂ (fun z => ℓ₂ z + anchorLog P z) U₂ := fun z hz =>
    (hℓ₂ z hz).add (anchorLog_analyticAt hP (hre₂ z hz))
  have hexpL₁ : ∀ z ∈ U₁, Complex.exp (ℓ₁ z + anchorLog P z) = anchoredSEM P N z := by
    intro z hz
    rw [Complex.exp_add, hexp₁ z hz, exp_anchorLog hP (hre₁ z hz),
      show anchoredSEM P N z = eulerHeadAnchor P z * completedSEM N z from rfl]
    ring
  have hexpL₂ : ∀ z ∈ U₂, Complex.exp (ℓ₂ z + anchorLog P z) = anchoredSEM P N z := by
    intro z hz
    rw [Complex.exp_add, hexp₂ z hz, exp_anchorLog hP (hre₂ z hz),
      show anchoredSEM P N z = eulerHeadAnchor P z * completedSEM N z from rfl]
    ring
  obtain ⟨k, hk, hdc⟩ := deckClass_neg_one_zpow_arg_variation hU₁ hU₁c hU₂ hU₂c
    hG₁ hG₂ hpG₁ hpG₂ hL₁ hL₂ hexpL₁ hexpL₂ hpP₁ hpP₂ hpM₁ hpM₂
  refine ⟨k, ?_, hdc⟩
  simp only [Complex.add_im] at hk
  linarith

end RHTower
