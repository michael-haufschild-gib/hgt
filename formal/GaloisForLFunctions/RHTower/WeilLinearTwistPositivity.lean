import GaloisForLFunctions.RHTower.WeilLinearTwistQuantization

/-!
# Positivity forbids a decreasing linear lock phase

Let `G` be a Herglotz producer for the weights `lam`.  Suppose that on the lower critical line

`G(1 − s) = κ₀ e^{iηx} e^{iβ₀C(x)} G(s)`,  `s = ½ − 2ix`, `x > 0`,

with `C` monotone and `C(x) = O(x^α)`, `α < 1`.

**Theorem** (`linear_twist_slope_nonneg`).  Then `η ≥ 0`.

Together with the quantization theorem (`linear_twist_slope_nonpos`) this gives `η = 0`, and the
monotone twist theorem gives `lam = Λ` and RH (`linear_twist_rigidity`).

**Proof.**
* `G(s̄) = conj G(s)` (`G_conj`): `G = s(s−1)Γ_ℝ(s) exp(Σ lam(n) n^{-s}/log n)` has real
  coefficients on `Re s > 1`, and the identity theorem extends this.
* `G = G(2) e^{P}` with `P' = Φ`.  Since `Re Φ ≥ 0`, the phase `x ↦ −2 Im P(σ − 2ix)` is
  nondecreasing on every line `Re s = σ > ½`.
* Near a boundary point where `G ≠ 0`, a continuous logarithm of `G` extends `P` up to the line.
  There the lock reads `e^{i(q(x) − β₀C(x))} = κ₀` with `q(x) = −2 Im P(½ − 2ix) − ηx`.  The
  function `q` is continuous and increases at rate at least `−η`.  An integer-valued function of the
  form continuous + monotone is monotone on intervals, so `β₀ ΔC ≥ −η Δx` near every such point
  (`local_lock_growth`).
* The zeros of `G` on the line are Lebesgue-null between two non-zeros: by Tonelli,
  `∫∫ Re Φ(σ − 2ix) dσ dx < ∞`, so `∫ Re Φ(σ − 2ix) dσ < ∞` for almost every `x`, and then
  `|G(½ − 2ix)| ≥ |G(σ₀ − 2ix)| e^{−∫ Re Φ} > 0`.
* `G` does not vanish on any far half-line, by the reflected radial limit `β/π ≠ 0`.
* So `C' ≥ −η/β₀` almost everywhere far out, and the Stieltjes measure of `C` grows linearly.
  This contradicts `C = O(x^α)`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-! ### Real structure of a producer -/

theorem lamLog_conj (lam : ℕ → ℝ) (n : ℕ) : conj (lamLog lam n) = lamLog lam n := by
  unfold lamLog
  split_ifs <;> simp only [map_div₀, Complex.conj_ofReal, map_zero]

theorem LSeries_lamLog_conj (lam : ℕ → ℝ) (s : ℂ) :
    LSeries (lamLog lam) (conj s) = conj (LSeries (lamLog lam) s) := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn, if_false, map_div₀, natCast_cpow_conj, lamLog_conj]

theorem bigG_conj (lam : ℕ → ℝ) (s : ℂ) : bigG lam (conj s) = conj (bigG lam s) := by
  unfold bigG zetaOf
  rw [LSeries_lamLog_conj, Complex.exp_conj, Gammaℝ_conj]
  simp only [map_mul, map_sub, map_one]

/-- **A producer has real coefficients:** `G(s̄) = conj G(s)` on `Re s ≥ ½`. -/
theorem G_conj {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) : G (conj s) = conj (G s) := by
  set U : Set ℂ := {z | 1 / 2 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have hGdU : DifferentiableOn ℂ G U := fun z hz => (hGd z hz).differentiableAt.differentiableWithinAt
  set g : ℂ → ℂ := (starRingEnd ℂ) ∘ G ∘ (starRingEnd ℂ) with hg
  have hgd : DifferentiableOn ℂ g U := by
    intro z hz
    have hcz : conj z ∈ U := by simpa [hU] using hz
    have h := ((hGdU (conj z) hcz).differentiableAt (hUo.mem_nhds hcz)).conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have h2 : (2 : ℂ) ∈ U := show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num
  have heq : G =ᶠ[𝓝 2] g := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)
    filter_upwards [hV] with z hz
    have hz' : 1 < (conj z).re := by simpa using hz
    simp only [hg, Function.comp_apply]
    rw [G_eq_bigG hsl hid hGd hG2 hz, G_eq_bigG hsl hid hGd hG2 hz', bigG_conj, Complex.conj_conj]
  have hEq := (hGdU.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hgd.analyticOnNhd hUo) hUc h2 heq
  have hGcl : ContinuousOn G {z : ℂ | 1 / 2 ≤ z.re} := fun z hz =>
    (hGc z hz).continuousWithinAt
  have hgc : ContinuousOn g {z : ℂ | 1 / 2 ≤ z.re} := by
    refine Complex.continuous_conj.comp_continuousOn (hGcl.comp Complex.continuous_conj.continuousOn
      fun z hz => ?_)
    show 1 / 2 ≤ (conj z).re
    simpa using hz
  have hclosed : EqOn G g {z : ℂ | 1 / 2 ≤ z.re} :=
    hEq.of_subset_closure hGcl hgc (fun z (hz : 1 / 2 < z.re) => show 1 / 2 ≤ z.re from hz.le)
      (by rw [Complex.closure_setOf_lt_re])
  have := hclosed (show 1 / 2 ≤ (conj s).re by simpa using hs)
  simp only [hg, Function.comp_apply, Complex.conj_conj] at this
  rw [this]

theorem bigG_two_conj (lam : ℕ → ℝ) : conj (bigG lam 2) = bigG lam 2 := by
  have h := bigG_conj lam 2
  rw [show conj (2 : ℂ) = 2 from Complex.conj_ofNat 2] at h
  exact h.symm


/-! ### The logarithm of a producer and its vertical phase -/

/-- The point `σ − 2ix`; on the critical line `vpt ½ x = lineS (−x)`. -/
def vpt (σ x : ℝ) : ℂ := (σ : ℂ) + ((-(2 * x) : ℝ) : ℂ) * I

@[simp] theorem vpt_re (σ x : ℝ) : (vpt σ x).re = σ := by simp [vpt]

theorem lineS_neg_eq_vpt (x : ℝ) : lineS (-x) = vpt (1 / 2) x := by
  rw [lineS_eq]; unfold vpt; push_cast; ring

theorem continuous_vpt_fst (x : ℝ) : Continuous fun σ : ℝ => vpt σ x := by
  unfold vpt; fun_prop

theorem hasDerivAt_vpt (σ x : ℝ) : HasDerivAt (fun x : ℝ => vpt σ x) (-2 * I) x := by
  have h1 : HasDerivAt (fun x : ℝ => (((-(2 * x)) : ℝ) : ℂ)) (((-(2 * 1)) : ℝ) : ℂ) x :=
    ((hasDerivAt_id x).const_mul 2).neg.ofReal_comp
  have h2 := (h1.mul_const I).const_add (σ : ℂ)
  refine h2.congr_deriv ?_
  push_cast; ring

/-- **A producer is `G(2) e^{P}` with `P' = Φ`** on `Re s > ½`. -/
theorem exists_log_producer {Φ G : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) :
    ∃ P : ℂ → ℂ, (∀ s : ℂ, 1 / 2 < s.re → HasDerivAt P (Φ s) s) ∧
      ∀ s : ℂ, 1 / 2 < s.re → G s = G 2 * cexp (P s) := by
  obtain ⟨P₀, hP₀⟩ := isExactOn_rightHalfPlane hΦd
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  set H : ℂ → ℂ := fun s => G s * cexp (-P₀ s) with hH
  have hHd : ∀ s ∈ U, HasDerivAt H 0 s := by
    intro s hs
    have h := (hGd s hs).mul (hP₀ s hs).neg.cexp
    refine h.congr_deriv ?_
    ring
  have hHdiff : DifferentiableOn ℂ H U := fun s hs => (hHd s hs).differentiableAt.differentiableWithinAt
  have hH0 : EqOn (deriv H) 0 U := fun s hs => (hHd s hs).deriv
  have h2 : (2 : ℂ) ∈ U := show (1 / 2 : ℝ) < (2 : ℂ).re by norm_num
  refine ⟨fun s => P₀ s - P₀ 2, fun s hs => (hP₀ s hs).sub_const _, fun s hs => ?_⟩
  have hc := hUo.is_const_of_deriv_eq_zero hUc hHdiff hH0 hs h2
  simp only [hH] at hc
  have e : G s = G s * cexp (-P₀ s) * cexp (P₀ s) := by
    rw [mul_assoc, ← Complex.exp_add]; simp
  rw [e, hc, mul_assoc, ← Complex.exp_add]
  congr 2; ring

/-- **The vertical phase is monotone**: `x ↦ Im P(σ − 2ix)` is antitone for `σ > ½`. -/
theorem antitone_im_vpt {Φ P : ℂ → ℂ} (hP : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt P (Φ s) s)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Antitone fun x : ℝ => (P (vpt σ x)).im := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (P (vpt σ x)).im)
      ((Φ (vpt σ x) * (-2 * I)).im) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => P (vpt σ x)) (Φ (vpt σ x) * (-2 * I)) x :=
      (hP (vpt σ x) (by simpa using hσ)).comp x (hasDerivAt_vpt σ x)
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h1)
  refine antitone_of_deriv_nonpos (fun x => (hd x).differentiableAt) fun x => ?_
  rw [(hd x).deriv]
  have h := hΦre (vpt σ x) (by simpa using hσ)
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]
  norm_num
  linarith

/-- **A continuous logarithm up to the line** near a boundary point where `G ≠ 0`. -/
theorem exists_local_log {Φ G P : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s)
    (hP : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt P (Φ s) s)
    (hPG : ∀ s : ℂ, 1 / 2 < s.re → G s = G 2 * cexp (P s))
    {b : ℂ} (hb : 1 / 2 ≤ b.re) (hGb : G b ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ L : ℂ → ℂ, ContinuousOn L (Metric.ball b r ∩ {s : ℂ | 1 / 2 ≤ s.re}) ∧
      (∀ s ∈ Metric.ball b r, 1 / 2 ≤ s.re → G s = G 2 * cexp (L s)) ∧
      (∀ s ∈ Metric.ball b r, 1 / 2 < s.re → L s = P s) := by
  have hGbn : 0 < ‖G b‖ := norm_pos_iff.mpr hGb
  obtain ⟨r, hr0, hr⟩ := Metric.continuousAt_iff.mp (hGc b hb) ‖G b‖ hGbn
  have hslit : ∀ s ∈ Metric.ball b r, G s / G b ∈ slitPlane := by
    intro s hs
    have h := hr (Metric.mem_ball.mp hs)
    rw [dist_eq_norm] at h
    have e : G s / G b = 1 + (G s - G b) / G b := by field_simp; ring
    rw [e]
    apply mem_slitPlane_of_norm_lt_one
    rw [norm_div, div_lt_one hGbn]; exact h
  have hGs : ∀ s ∈ Metric.ball b r, G s ≠ 0 := by
    intro s hs h0
    have := hslit s hs
    rw [h0, zero_div] at this
    exact slitPlane_ne_zero this rfl
  set ℓ : ℂ → ℂ := fun s => Complex.log (G s / G b) with hℓ
  have hℓc : ContinuousOn ℓ (Metric.ball b r ∩ {s : ℂ | 1 / 2 ≤ s.re}) := by
    intro s hs
    have hca : ContinuousAt (fun t => G t / G b) s := (hGc s hs.2).div_const (G b)
    have hlog : ContinuousAt Complex.log ((fun t => G t / G b) s) := continuousAt_clog (hslit s hs.1)
    exact (ContinuousAt.comp (x := s) hlog hca).continuousWithinAt
  set W : Set ℂ := Metric.ball b r ∩ {s : ℂ | 1 / 2 < s.re} with hW
  have hWo : IsOpen W := Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hWc : IsPreconnected W :=
    ((convex_ball b r).inter (convex_halfSpace_re_gt (1 / 2))).isPreconnected
  have hdiff : ∀ s ∈ W, HasDerivAt (fun s => P s - ℓ s) 0 s := by
    intro s hs
    have h1 := ((hGd s hs.2).div_const (G b)).clog (hslit s hs.1)
    refine ((hP s hs.2).sub h1).congr_deriv ?_
    have hG0 := hGs s hs.1
    have hGb0 := hGb
    field_simp
    ring
  have hdW : DifferentiableOn ℂ (fun s => P s - ℓ s) W := fun s hs =>
    (hdiff s hs).differentiableAt.differentiableWithinAt
  have hd0 : EqOn (deriv fun s => P s - ℓ s) 0 W := fun s hs => (hdiff s hs).deriv
  set w₀ : ℂ := b + ((r / 2 : ℝ) : ℂ) with hw₀
  have hw₀W : w₀ ∈ W := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, hw₀, add_sub_cancel_left, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · show 1 / 2 < (b + ((r / 2 : ℝ) : ℂ)).re
      simp only [Complex.add_re, Complex.ofReal_re]; linarith
  set c' : ℂ := P w₀ - ℓ w₀ with hc'
  have hPℓ : ∀ s ∈ W, P s = ℓ s + c' := by
    intro s hs
    have := hWo.is_const_of_deriv_eq_zero hWc hdW hd0 hs hw₀W
    rw [hc']; linear_combination this
  have hGw₀ := hGs w₀ hw₀W.1
  have hc'G : G 2 * cexp c' = G b := by
    have h1 := hPG w₀ hw₀W.2
    rw [hPℓ w₀ hw₀W, Complex.exp_add, hℓ] at h1
    simp only at h1
    rw [Complex.exp_log (slitPlane_ne_zero (hslit w₀ hw₀W.1))] at h1
    have h3 : G w₀ * (G 2 * cexp c') = G w₀ * G b := by
      calc G w₀ * (G 2 * cexp c') = (G 2 * (G w₀ / G b * cexp c')) * G b := by
            field_simp
        _ = G w₀ * G b := by rw [← h1]
    exact mul_left_cancel₀ hGw₀ h3
  refine ⟨r, hr0, fun s => ℓ s + c', hℓc.add continuousOn_const, fun s hs _ => ?_,
    fun s hs hs' => (hPℓ s ⟨hs, hs'⟩).symm⟩
  simp only [hℓ]
  rw [Complex.exp_add, Complex.exp_log (slitPlane_ne_zero (hslit s hs)), mul_comm (G s / G b),
    ← mul_assoc, hc'G]
  field_simp


/-! ### Integer-valued sums of continuous and monotone functions -/

/-- The equally spaced points `a + i(b − a)/N`. -/
theorem mem_Icc_grid {a b : ℝ} (hab : a ≤ b) {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i ≤ N) :
    a + i * ((b - a) / N) ∈ Icc a b := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hiN : (i : ℝ) ≤ N := by exact_mod_cast hi
  have h0 : 0 ≤ (i : ℝ) * ((b - a) / N) := by
    apply mul_nonneg (Nat.cast_nonneg i); apply div_nonneg <;> linarith
  have h1 : (i : ℝ) * ((b - a) / N) ≤ b - a := by
    rw [mul_div_assoc', div_le_iff₀ hNr]; nlinarith
  constructor <;> linarith

/-- **An integer-valued `f + g`, with `f` continuous and `g` antitone, is antitone.** -/
theorem int_valued_add_antitone {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : AntitoneOn g (Icc a b))
    (hk : ∀ x ∈ Icc a b, ∃ n : ℤ, f x + g x = n) : f b + g b ≤ f a + g a := by
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) 1 one_pos
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hNpos : 0 < N := by
    have : (0 : ℝ) ≤ (b - a) / δ := div_nonneg (by linarith) hδ0.le
    exact_mod_cast (lt_of_le_of_lt this hN)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set h : ℝ := (b - a) / N with hh
  have hh0 : 0 ≤ h := div_nonneg (by linarith) hNr.le
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ hNr]
    rw [div_lt_iff₀ hδ0] at hN
    linarith
  set p : ℕ → ℝ := fun i => a + i * h with hp
  have hstep : ∀ i, i < N → f (p (i + 1)) + g (p (i + 1)) ≤ f (p i) + g (p i) := by
    intro i hi
    have hm1 := mem_Icc_grid hab hNpos (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hi))
    have hm2 := mem_Icc_grid hab hNpos (Nat.succ_le_of_lt hi)
    have hd : dist (p (i + 1)) (p i) < δ := by
      rw [Real.dist_eq, hp]; push_cast
      rw [show a + ((i : ℝ) + 1) * h - (a + i * h) = h by ring, abs_of_nonneg hh0]; exact hhδ
    have hfd := hδ _ hm2 _ hm1 hd
    rw [Real.dist_eq] at hfd
    have hgle : g (p (i + 1)) ≤ g (p i) := hg hm1 hm2 (by rw [hp]; push_cast; nlinarith)
    obtain ⟨n₁, hn₁⟩ := hk _ hm2
    obtain ⟨n₂, hn₂⟩ := hk _ hm1
    have hlt : f (p (i + 1)) + g (p (i + 1)) < f (p i) + g (p i) + 1 := by
      have := (abs_lt.mp hfd).2; linarith
    rw [hn₁, hn₂] at hlt ⊢
    have : n₁ < n₂ + 1 := by exact_mod_cast hlt
    exact_mod_cast (show n₁ ≤ n₂ by omega)
  have hall : ∀ i, i ≤ N → f (p i) + g (p i) ≤ f a + g a := by
    intro i hi
    induction i with
    | zero => simp [hp]
    | succ i ih => exact (hstep i (by omega)).trans (ih (by omega))
  have hpN : p N = b := by rw [hp, hh]; field_simp; ring
  rw [← hpN]; exact hall N le_rfl

/-- **An integer-valued function cannot be strictly increasing on an interval.** -/
theorem false_of_int_valued_strictMonoOn {k : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hk : ∀ x ∈ Icc a b, ∃ n : ℤ, k x = n) (hmono : StrictMonoOn k (Icc a b)) : False := by
  obtain ⟨N, hN⟩ := exists_nat_gt (k b - k a)
  have hNpos : 0 < N + 1 := Nat.succ_pos N
  set h : ℝ := (b - a) / (N + 1 : ℕ) with hh
  have hNr : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hh0 : 0 < h := div_pos (by linarith) hNr
  set p : ℕ → ℝ := fun i => a + i * h with hp
  have hstep : ∀ i, i < N + 1 → k (p i) + 1 ≤ k (p (i + 1)) := by
    intro i hi
    have hm1 := mem_Icc_grid hab.le hNpos (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hi))
    have hm2 := mem_Icc_grid hab.le hNpos (Nat.succ_le_of_lt hi)
    have hlt := hmono hm1 hm2 (by
      rw [← hh]; push_cast; nlinarith)
    obtain ⟨n₁, hn₁⟩ := hk _ hm1
    obtain ⟨n₂, hn₂⟩ := hk _ hm2
    rw [hn₁, hn₂] at hlt ⊢
    have : n₁ < n₂ := by exact_mod_cast hlt
    exact_mod_cast (show n₁ + 1 ≤ n₂ by omega)
  have hall : ∀ i, i ≤ N + 1 → k a + i ≤ k (p i) := by
    intro i hi
    induction i with
    | zero => simp [hp]
    | succ i ih =>
        have := hstep i (by omega)
        have := ih (by omega)
        push_cast; linarith
  have hpN : p (N + 1) = b := by rw [hp, hh]; field_simp; ring
  have := hall (N + 1) le_rfl
  rw [hpN] at this
  push_cast at this
  linarith


/-! ### The lock near a boundary non-zero -/

theorem dist_vpt (σ x x' : ℝ) : dist (vpt σ x) (vpt σ x') = 2 * |x - x'| := by
  rw [dist_eq_norm]
  have e : vpt σ x - vpt σ x' = ((-(2 * (x - x')) : ℝ) : ℂ) * I := by unfold vpt; push_cast; ring
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul,
    abs_two]

/-- The boundary value of a local logarithm is the limit of interior values along `Re s = σ ↓ ½`. -/
theorem tendsto_im_local_log {L : ℂ → ℂ} {b : ℂ} {r : ℝ}
    (hL : ContinuousOn L (Metric.ball b r ∩ {s : ℂ | 1 / 2 ≤ s.re})) {x : ℝ}
    (hx : vpt (1 / 2) x ∈ Metric.ball b r) :
    Tendsto (fun σ : ℝ => (L (vpt σ x)).im) (𝓝[>] (1 / 2)) (𝓝 (L (vpt (1 / 2) x)).im) := by
  have hmem : vpt (1 / 2) x ∈ Metric.ball b r ∩ {s : ℂ | 1 / 2 ≤ s.re} := ⟨hx, by simp⟩
  have hcw := (hL _ hmem).tendsto
  have hv : Tendsto (fun σ : ℝ => vpt σ x) (𝓝[>] (1 / 2))
      (𝓝[Metric.ball b r ∩ {s : ℂ | 1 / 2 ≤ s.re}] (vpt (1 / 2) x)) := by
    rw [tendsto_nhdsWithin_iff]
    have ht : Tendsto (fun σ : ℝ => vpt σ x) (𝓝[>] (1 / 2)) (𝓝 (vpt (1 / 2) x)) :=
      ((continuous_vpt_fst x).tendsto _).mono_left nhdsWithin_le_nhds
    refine ⟨ht, ?_⟩
    filter_upwards [ht (Metric.isOpen_ball.mem_nhds hx), self_mem_nhdsWithin] with σ h1 h2
    exact ⟨h1, by simp only [mem_setOf_eq, vpt_re]; exact (mem_Ioi.mp h2).le⟩
  exact (Complex.continuous_im.tendsto _).comp (hcw.comp hv)

/-- **The boundary phase is monotone** where a continuous logarithm exists. -/
theorem boundary_phase_antitone {Φ P L : ℂ → ℂ}
    (hP : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt P (Φ s) s)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re) {b : ℂ} {r : ℝ}
    (hL : ContinuousOn L (Metric.ball b r ∩ {s : ℂ | 1 / 2 ≤ s.re}))
    (hLP : ∀ s ∈ Metric.ball b r, 1 / 2 < s.re → L s = P s) {x x' : ℝ} (hxx : x ≤ x')
    (hx : vpt (1 / 2) x ∈ Metric.ball b r) (hx' : vpt (1 / 2) x' ∈ Metric.ball b r) :
    (L (vpt (1 / 2) x')).im ≤ (L (vpt (1 / 2) x)).im := by
  have ev : ∀ y, vpt (1 / 2) y ∈ Metric.ball b r →
      ∀ᶠ σ in 𝓝[>] (1 / 2 : ℝ), L (vpt σ y) = P (vpt σ y) := by
    intro y hy
    have ht : Tendsto (fun σ : ℝ => vpt σ y) (𝓝[>] (1 / 2)) (𝓝 (vpt (1 / 2) y)) :=
      ((continuous_vpt_fst y).tendsto _).mono_left nhdsWithin_le_nhds
    filter_upwards [ht (Metric.isOpen_ball.mem_nhds hy), self_mem_nhdsWithin] with σ h1 h2
    exact hLP _ h1 (by simpa using h2)
  refine le_of_tendsto_of_tendsto (tendsto_im_local_log hL hx') (tendsto_im_local_log hL hx) ?_
  filter_upwards [ev x hx, ev x' hx', self_mem_nhdsWithin] with σ h1 h2 h3
  rw [h1, h2]
  exact antitone_im_vpt hP hΦre (mem_Ioi.mp h3) hxx

/-- **The lock forces local growth of `C`.**  Let `G` be a Herglotz producer whose lower-line lock is
`G(1 − s) = κ₀ e^{iηx} e^{iβ₀C(x)} G(s)`, `s = ½ − 2ix`, with `η < 0` and `C` monotone.  At a point
`x₀ > 0` with `G(½ − 2ix₀) ≠ 0`: `β₀ > 0`, and `β₀(C(x') − C(x)) ≥ −η(x' − x)` for `x ≤ x'` near
`x₀`. -/
theorem local_lock_growth {lam : ℕ → ℝ} {Φ G P : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (hG20 : G 2 ≠ 0)
    (hP : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt P (Φ s) s)
    (hPG : ∀ s : ℂ, 1 / 2 < s.re → G s = G 2 * cexp (P s))
    {C : ℝ → ℝ} (hC : Monotone C) {κ₀ : ℂ} {η β₀ : ℝ} (hη : η < 0)
    (hlock : ∀ x : ℝ, 0 < x → G (1 - vpt (1 / 2) x) =
      κ₀ * cexp (((η * x : ℝ) : ℂ) * I) * cexp (((β₀ * C x : ℝ) : ℂ) * I) * G (vpt (1 / 2) x))
    {x₀ : ℝ} (hx₀ : 0 < x₀) (hG0 : G (vpt (1 / 2) x₀) ≠ 0) :
    0 < β₀ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x x' : ℝ, x₀ - δ < x → x ≤ x' → x' < x₀ + δ →
      -η * (x' - x) ≤ β₀ * (C x' - C x) := by
  have hpi := Real.pi_pos
  obtain ⟨r, hr0, L, hLc, hGL, hLP⟩ :=
    exists_local_log hGc hGd hP hPG (b := vpt (1 / 2) x₀) (by simp) hG0
  set δ : ℝ := min (r / 4) (x₀ / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hinball : ∀ x, x₀ - δ < x → x < x₀ + δ → vpt (1 / 2) x ∈ Metric.ball (vpt (1 / 2) x₀) r := by
    intro x h1 h2
    rw [Metric.mem_ball, dist_vpt]
    have : |x - x₀| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    have : δ ≤ r / 4 := min_le_left _ _
    linarith
  have hpos : ∀ x, x₀ - δ < x → 0 < x := by
    intro x h1
    have : δ ≤ x₀ / 2 := min_le_right _ _
    linarith
  -- the lock in terms of the boundary phase
  have hphase : ∀ x, x₀ - δ < x → x < x₀ + δ →
      cexp ((((-2 * (L (vpt (1 / 2) x)).im - η * x - β₀ * C x) : ℝ) : ℂ) * I) = κ₀ := by
    intro x h1 h2
    have hb := hinball x h1 h2
    have hre : (1 / 2 : ℝ) ≤ (vpt (1 / 2) x).re := by simp
    have hG := hGL _ hb hre
    have hconj : 1 - vpt (1 / 2) x = conj (vpt (1 / 2) x) := by
      rw [← lineS_neg_eq_vpt, one_sub_lineS_eq_conj]
    have hl := hlock x (hpos x h1)
    rw [hconj, G_conj hsl hid hGc hGd hG2 hre, hG, map_mul, ← Complex.exp_conj, hG2,
      bigG_two_conj, ← hG2] at hl
    have hcancel : cexp (conj (L (vpt (1 / 2) x))) =
        κ₀ * cexp (((η * x : ℝ) : ℂ) * I) * cexp (((β₀ * C x : ℝ) : ℂ) * I) *
          cexp (L (vpt (1 / 2) x)) := by
      apply mul_left_cancel₀ hG20
      linear_combination hl
    have e1 : conj (L (vpt (1 / 2) x)) = L (vpt (1 / 2) x) +
        (((-2 * (L (vpt (1 / 2) x)).im : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp; ring
    rw [e1, Complex.exp_add] at hcancel
    have hne : cexp (L (vpt (1 / 2) x)) ≠ 0 := Complex.exp_ne_zero _
    have h3 : cexp ((((-2 * (L (vpt (1 / 2) x)).im : ℝ) : ℂ) * I)) =
        κ₀ * cexp (((η * x : ℝ) : ℂ) * I) * cexp (((β₀ * C x : ℝ) : ℂ) * I) := by
      apply mul_left_cancel₀ hne; linear_combination hcancel
    have e2 : ((((-2 * (L (vpt (1 / 2) x)).im - η * x - β₀ * C x) : ℝ) : ℂ) * I) =
        (((-2 * (L (vpt (1 / 2) x)).im : ℝ) : ℂ) * I) - (((η * x : ℝ) : ℂ) * I) -
          (((β₀ * C x : ℝ) : ℂ) * I) := by push_cast; ring
    rw [e2, Complex.exp_sub, Complex.exp_sub, h3]
    field_simp
  -- the integer-valued phase defect
  set c₀ : ℝ := -2 * (L (vpt (1 / 2) x₀)).im - η * x₀ - β₀ * C x₀ with hc₀
  have hδx₀ : x₀ - δ < x₀ := by linarith
  have hκ := hphase x₀ hδx₀ (by linarith)
  set f : ℝ → ℝ := fun x => (-2 * (L (vpt (1 / 2) x)).im - η * x - c₀) / (2 * Real.pi) with hf
  set g : ℝ → ℝ := fun x => -(β₀ * C x) / (2 * Real.pi) with hg
  have hint : ∀ x, x₀ - δ < x → x < x₀ + δ → ∃ n : ℤ, f x + g x = n := by
    intro x h1 h2
    have h := hphase x h1 h2
    have hκne : κ₀ ≠ 0 := by rw [← hκ]; exact Complex.exp_ne_zero _
    have h' : cexp (((((-2 * (L (vpt (1 / 2) x)).im - η * x - β₀ * C x) - c₀) : ℝ) : ℂ) * I) = 1 := by
      rw [show (((((-2 * (L (vpt (1 / 2) x)).im - η * x - β₀ * C x) - c₀) : ℝ) : ℂ) * I) =
          ((((-2 * (L (vpt (1 / 2) x)).im - η * x - β₀ * C x)) : ℝ) : ℂ) * I - ((c₀ : ℝ) : ℂ) * I by
        push_cast; ring, Complex.exp_sub, h, hκ, div_self hκne]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h'
    refine ⟨n, ?_⟩
    have hn' := congrArg Complex.im hn
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_add, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat,
      Complex.im_ofNat] at hn'
    have e2 : (2 * (Real.pi : ℂ)).re = 2 * Real.pi := by simp
    rw [e2] at hn'
    simp only [hf, hg]
    field_simp
    linarith
  -- continuity and monotonicity of `f`
  have hfc : ∀ a b, x₀ - δ < a → b < x₀ + δ → ContinuousOn f (Icc a b) := by
    intro a b ha hb x hx
    have hx1 : x₀ - δ < x := lt_of_lt_of_le ha hx.1
    have hx2 : x < x₀ + δ := lt_of_le_of_lt hx.2 hb
    have hmem : vpt (1 / 2) x ∈ Metric.ball (vpt (1 / 2) x₀) r ∩ {s : ℂ | 1 / 2 ≤ s.re} :=
      ⟨hinball x hx1 hx2, by simp⟩
    have hv : ContinuousWithinAt (fun y : ℝ => vpt (1 / 2) y) (Icc a b) x := by
      unfold vpt; fun_prop
    have hmaps : MapsTo (fun y : ℝ => vpt (1 / 2) y) (Icc a b)
        (Metric.ball (vpt (1 / 2) x₀) r ∩ {s : ℂ | 1 / 2 ≤ s.re}) := fun y hy =>
      ⟨hinball y (lt_of_lt_of_le ha hy.1) (lt_of_le_of_lt hy.2 hb), by simp⟩
    have hL' := (hLc _ hmem).comp hv hmaps
    exact ((((Complex.continuous_im.continuousWithinAt.comp hL' (mapsTo_univ _ _)).const_mul
      (-2)).sub (continuousWithinAt_id.const_mul η)).sub continuousWithinAt_const).div_const _
  have hfmono : ∀ x x', x₀ - δ < x → x ≤ x' → x' < x₀ + δ →
      -η * (x' - x) / (2 * Real.pi) ≤ f x' - f x := by
    intro x x' h1 hxx h2
    have hph := boundary_phase_antitone hP hΦre hLc hLP hxx (hinball x h1 (by linarith))
      (hinball x' (by linarith) h2)
    simp only [hf]
    rw [div_sub_div_same, div_le_div_iff_of_pos_right (by positivity)]
    linarith
  -- the sign of `β₀`
  have hβ : 0 < β₀ := by
    by_contra hβ
    push Not at hβ
    refine false_of_int_valued_strictMonoOn (k := fun x => f x + g x) (a := x₀ - δ / 2)
      (b := x₀ + δ / 2)
      (by linarith) (fun x hx => hint x (by linarith [hx.1]) (by linarith [hx.2])) ?_
    intro x hx x' hx' hxx
    have h1 := hfmono x x' (by linarith [hx.1]) hxx.le (by linarith [hx'.2])
    have h2 : g x ≤ g x' := by
      simp only [hg]
      rw [div_le_div_iff_of_pos_right (by positivity)]
      have := hC hxx.le
      nlinarith
    have h3 : 0 < -η * (x' - x) / (2 * Real.pi) := by
      apply div_pos _ (by positivity); nlinarith
    simp only
    linarith
  refine ⟨hβ, δ, hδ0, fun x x' h1 hxx h2 => ?_⟩
  have hga : AntitoneOn g (Icc x x') := by
    intro y _ y' _ hyy
    simp only [hg]
    rw [div_le_div_iff_of_pos_right (by positivity)]
    have := hC hyy
    nlinarith
  have hk := int_valued_add_antitone hxx (hfc x x' h1 h2) hga
    (fun y hy => hint y (by linarith [hy.1]) (by linarith [hy.2]))
  have hfm := hfmono x x' h1 hxx h2
  simp only [hg] at hk
  have hpi2 : 0 < 2 * Real.pi := by positivity
  have h4 : f x' - f x ≤ (β₀ * C x' - β₀ * C x) / (2 * Real.pi) := by
    rw [sub_div]
    have e1 : -(β₀ * C x') / (2 * Real.pi) = -(β₀ * C x' / (2 * Real.pi)) := neg_div _ _
    have e2 : -(β₀ * C x) / (2 * Real.pi) = -(β₀ * C x / (2 * Real.pi)) := neg_div _ _
    rw [e1, e2] at hk
    linarith
  have h5 : -η * (x' - x) / (2 * Real.pi) ≤ (β₀ * C x' - β₀ * C x) / (2 * Real.pi) := hfm.trans h4
  rw [div_le_div_iff_of_pos_right hpi2] at h5
  linarith


/-! ### The zeros on the line are null between two non-zeros -/

theorem continuousOn_re_phi_vpt {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re}) :
    ContinuousOn (fun p : ℝ × ℝ => (Φ (vpt p.2 p.1)).re) {p : ℝ × ℝ | 1 / 2 < p.2} := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => vpt p.2 p.1) {p : ℝ × ℝ | 1 / 2 < p.2} := by
    unfold vpt; fun_prop
  refine Complex.continuous_re.comp_continuousOn (hΦd.continuousOn.comp hc fun p hp => ?_)
  simpa using hp

theorem hasDerivAt_im_P_vpt {Φ P : ℂ → ℂ} (hP : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt P (Φ s) s)
    {σ : ℝ} (hσ : 1 / 2 < σ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (P (vpt σ x)).im) (-2 * (Φ (vpt σ x)).re) x := by
  have h1 : HasDerivAt (fun x : ℝ => P (vpt σ x)) (Φ (vpt σ x) * (-2 * I)) x :=
    (hP (vpt σ x) (by simpa using hσ)).comp x (hasDerivAt_vpt σ x)
  have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h1
  refine h2.congr_deriv ?_
  simp [Complex.mul_im]
  ring

theorem hasDerivAt_re_P_vpt {Φ P : ℂ → ℂ} (hP : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt P (Φ s) s)
    (x : ℝ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    HasDerivAt (fun σ : ℝ => (P (vpt σ x)).re) ((Φ (vpt σ x)).re) σ := by
  have hv : HasDerivAt (fun σ : ℝ => vpt σ x) 1 σ := by
    unfold vpt
    simpa using ((hasDerivAt_id σ).ofReal_comp).add_const (((-(2 * x) : ℝ) : ℂ) * I)
  have h1 : HasDerivAt (fun σ : ℝ => P (vpt σ x)) (Φ (vpt σ x) * 1) σ :=
    (hP (vpt σ x) (by simpa using hσ)).comp σ hv
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt σ h1
  refine h2.congr_deriv ?_
  simp

/-- Near a boundary non-zero, `Im P` stays bounded as `Re s ↓ ½`. -/
theorem exists_bound_im_P {Φ G P : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s)
    (hP : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt P (Φ s) s)
    (hPG : ∀ s : ℂ, 1 / 2 < s.re → G s = G 2 * cexp (P s))
    {x₀ : ℝ} (hG0 : G (vpt (1 / 2) x₀) ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + ρ → |(P (vpt σ x₀)).im| ≤ M := by
  obtain ⟨r, hr0, L, hLc, -, hLP⟩ :=
    exists_local_log hGc hGd hP hPG (b := vpt (1 / 2) x₀) (by simp) hG0
  have hin : ∀ σ ∈ Icc (1 / 2 : ℝ) (1 / 2 + r / 2), vpt σ x₀ ∈ Metric.ball (vpt (1 / 2) x₀) r := by
    intro σ hσ
    rw [Metric.mem_ball, dist_eq_norm]
    have e : vpt σ x₀ - vpt (1 / 2) x₀ = ((σ - 1 / 2 : ℝ) : ℂ) := by unfold vpt; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hσ.1])]
    linarith [hσ.2]
  have hcont : ContinuousOn (fun σ : ℝ => L (vpt σ x₀)) (Icc (1 / 2 : ℝ) (1 / 2 + r / 2)) :=
    hLc.comp (continuous_vpt_fst x₀).continuousOn fun σ hσ =>
      ⟨hin σ hσ, by simp only [mem_setOf_eq, vpt_re]; exact hσ.1⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨r / 2, by linarith, M, fun σ hσ1 hσ2 => ?_⟩
  have hmem : σ ∈ Icc (1 / 2 : ℝ) (1 / 2 + r / 2) := ⟨hσ1.le, hσ2⟩
  rw [← hLP _ (hin σ hmem) (by simpa using hσ1)]
  exact (Complex.abs_im_le_norm _).trans (hM σ hmem)

/-- **Boundary zeros are null between two non-zeros.**  If `G(½ − 2iA) ≠ 0` and `G(½ − 2iB) ≠ 0`,
then `G(½ − 2ix) ≠ 0` for almost every `x ∈ (A, B)`. -/
theorem ae_ne_zero_of_ends {Φ G P : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s)
    (hG20 : G 2 ≠ 0)
    (hP : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt P (Φ s) s)
    (hPG : ∀ s : ℂ, 1 / 2 < s.re → G s = G 2 * cexp (P s))
    {A B : ℝ} (hAB : A ≤ B) (hA : G (vpt (1 / 2) A) ≠ 0) (hB : G (vpt (1 / 2) B) ≠ 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo A B)), G (vpt (1 / 2) x) ≠ 0 := by
  obtain ⟨ρA, hρA, MA, hMA⟩ := exists_bound_im_P hGc hGd hP hPG hA
  obtain ⟨ρB, hρB, MB, hMB⟩ := exists_bound_im_P hGc hGd hP hPG hB
  set ρ : ℝ := min ρA ρB with hρ
  have hρ0 : 0 < ρ := lt_min hρA hρB
  set S : Set ℝ := Ioo (1 / 2 : ℝ) (1 / 2 + ρ) with hS
  set T : Set ℝ := Ioo A B with hT
  set F : ℝ → ℝ → ENNReal := fun x σ => ENNReal.ofReal ((Φ (vpt σ x)).re) with hF
  have hcont := continuousOn_re_phi_vpt hΦd
  -- the vertical integrals are bounded
  have hvert : ∀ σ ∈ S, ∫⁻ x in T, F x σ ≤ ENNReal.ofReal ((MA + MB) / 2) := by
    intro σ hσ
    have hσ1 : 1 / 2 < σ := hσ.1
    have hcx : ContinuousOn (fun x : ℝ => (Φ (vpt σ x)).re) (Icc A B) := by
      have : Continuous fun x : ℝ => (σ, x).swap := by fun_prop
      refine (hcont.comp (Continuous.continuousOn (by fun_prop : Continuous fun x : ℝ => (x, σ))) ?_)
      intro x _; exact hσ1
    have hint : IntegrableOn (fun x : ℝ => (Φ (vpt σ x)).re) T :=
      (hcx.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => hΦre _ (by simpa using hσ1))]
    apply ENNReal.ofReal_le_ofReal
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => (P (vpt σ x)).im) (f' := fun x => -2 * (Φ (vpt σ x)).re)
      (a := A) (b := B) (fun x _ => hasDerivAt_im_P_vpt hP hσ1 x)
      ((hcx.const_smul (-2 : ℝ)).intervalIntegrable_of_Icc hAB)
    rw [intervalIntegral.integral_of_le hAB, integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_const_mul] at hftc
    have h1 := hMA σ hσ1 (by linarith [hσ.2, min_le_left ρA ρB])
    have h2 := hMB σ hσ1 (by linarith [hσ.2, min_le_right ρA ρB])
    have := abs_le.mp h1
    have := abs_le.mp h2
    linarith
  have hfin : ∫⁻ σ in S, ∫⁻ x in T, F x σ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' measurableSet_Ioo hvert)
    rw [setLIntegral_const, Real.volume_Ioo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  -- Tonelli
  have hmeas : AEMeasurable (Function.uncurry F) ((volume.restrict T).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    refine (ContinuousOn.aemeasurable ?_ (measurableSet_Ioo.prod measurableSet_Ioo))
    refine ENNReal.continuous_ofReal.comp_continuousOn (hcont.mono fun p hp => hp.2.1)
  have hswap := lintegral_lintegral_swap hmeas
  rw [← hswap] at hfin
  have hae := ae_lt_top' (hmeas.lintegral_prod_right') hfin
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx₀ hxT
  have hx : ∫⁻ σ in S, F x σ < ⊤ := hx₀
  -- a horizontal lower bound for `|G|`
  set σ₁ : ℝ := 1 / 2 + ρ / 2 with hσ₁
  have hσ₁S : σ₁ ∈ S := ⟨by linarith, by linarith⟩
  set I₀ : ℝ := (∫⁻ σ in S, F x σ).toReal with hI₀
  have hbound : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ σ₁ →
      (P (vpt σ₁ x)).re - I₀ ≤ (P (vpt σ x)).re := by
    intro σ hσ hσσ
    have hcσ : ContinuousOn (fun σ' : ℝ => (Φ (vpt σ' x)).re) (Icc σ σ₁) :=
      hcont.comp (Continuous.continuousOn (by fun_prop : Continuous fun σ' : ℝ => (x, σ')))
        fun σ' hσ' => show 1 / 2 < σ' from lt_of_lt_of_le hσ hσ'.1
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun σ' : ℝ => (P (vpt σ' x)).re) (f' := fun σ' => (Φ (vpt σ' x)).re)
      (a := σ) (b := σ₁) (fun σ' hσ' => hasDerivAt_re_P_vpt hP x (by
        rw [Set.uIcc_of_le hσσ] at hσ'; exact lt_of_lt_of_le hσ hσ'.1))
      (hcσ.intervalIntegrable_of_Icc hσσ)
    rw [intervalIntegral.integral_of_le hσσ] at hftc
    have hintσ : IntegrableOn (fun σ' : ℝ => (Φ (vpt σ' x)).re) (Ioc σ σ₁) :=
      (hcσ.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hle : ∫ σ' in Ioc σ σ₁, (Φ (vpt σ' x)).re ≤ I₀ := by
      rw [← ENNReal.ofReal_le_iff_le_toReal hx.ne, ofReal_integral_eq_lintegral_ofReal hintσ
        ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun σ' hσ' =>
          hΦre _ (by simp only [vpt_re]; exact lt_trans hσ hσ'.1)))]
      exact lintegral_mono_set (fun σ' hσ' => ⟨lt_trans hσ hσ'.1, by linarith [hσ'.2]⟩)
    linarith
  have hlow : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ σ₁ →
      ‖G 2‖ * Real.exp ((P (vpt σ₁ x)).re - I₀) ≤ ‖G (vpt σ x)‖ := by
    intro σ hσ hσσ
    rw [hPG (vpt σ x) (by simpa using hσ), norm_mul, Complex.norm_exp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hbound σ hσ hσσ)) (norm_nonneg _)
  have hpos : 0 < ‖G 2‖ * Real.exp ((P (vpt σ₁ x)).re - I₀) :=
    mul_pos (norm_pos_iff.mpr hG20) (Real.exp_pos _)
  have htend : Tendsto (fun σ : ℝ => ‖G (vpt σ x)‖) (𝓝[>] (1 / 2)) (𝓝 ‖G (vpt (1 / 2) x)‖) :=
    ((hGc _ (by simp)).norm.tendsto.comp ((continuous_vpt_fst x).tendsto _)).mono_left
      nhdsWithin_le_nhds
  have hge := ge_of_tendsto htend (by
    filter_upwards [Ioo_mem_nhdsGT (show (1 / 2 : ℝ) < σ₁ by linarith)] with σ hσ
    exact hlow σ hσ.1 hσ.2.le)
  intro h0
  rw [h0, norm_zero] at hge
  linarith


/-! ### The producer does not vanish on a far half-line -/

/-- **A producer does not vanish on any far half-line of the lower critical line.**  Otherwise the
reflected integral `ε J(ε + i)` is carried by a compact range of `t` and tends to `0`, not to
`β/π ≠ 0`. -/
theorem exists_ne_zero_beyond {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (X : ℝ) : ∃ x : ℝ, X ≤ x ∧ 0 < x ∧ G (vpt (1 / 2) x) ≠ 0 := by
  have hpi := Real.pi_pos
  by_contra hcon
  push Not at hcon
  set X' : ℝ := max X 1 with hX'
  have hX'1 : 1 ≤ X' := le_max_right _ _
  have hzero : ∀ t : ℝ, t ≤ -X' → phiStar G t = 0 := by
    intro t ht
    have hx : G (vpt (1 / 2) (-t)) = 0 :=
      hcon (-t) (by linarith [le_max_left X 1]) (by linarith)
    have hl : lineS t = vpt (1 / 2) (-t) := by rw [← lineS_neg_eq_vpt, neg_neg]
    unfold phiStar
    rw [one_sub_lineS_eq_conj, G_conj hsl hid hGc hGd hG2 (le_of_eq (lineS_re t).symm), hl, hx,
      map_zero, zero_div]
  have hβ : betaG G ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))
      two_ne_zero
  have hrefl := tendsto_lower_reflected_radial hsl hΦre hid hGc hGd hG2 (le_refl 1)
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  set K₀ : ℝ := 1 / (2 * Real.pi) * ((2 * CB * (1 + X') ^ N * 3) * X') with hK₀
  have hbound : ∀ ε : ℝ, 0 < ε →
      ‖(ε : ℂ) * defectLaplace ((Iio (0 : ℝ)).indicator (phiStar G))
        ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)‖ ≤ ε * K₀ := by
    intro ε hε
    set τ : ℂ := (ε : ℂ) + ((1 : ℕ) : ℂ) * I with hτ
    have hτre : 0 < τ.re := by simp [hτ]; exact hε
    have hτ1 : 1 ≤ ‖τ‖ := by
      have h := Complex.abs_im_le_norm τ
      have him : τ.im = 1 := by simp [hτ]
      rw [him, abs_one] at h; exact h
    have hind : (fun t => (Iio (0 : ℝ)).indicator (phiStar G) t * pairKernel (2 * t) τ) =
        (Ioo (-X') 0).indicator (fun t => phiStar G t * pairKernel (2 * t) τ) := by
      funext t
      by_cases h1 : t < 0
      · by_cases h2 : -X' < t
        · rw [Set.indicator_of_mem (show t ∈ Iio (0 : ℝ) from h1),
            Set.indicator_of_mem (show t ∈ Ioo (-X') 0 from ⟨h2, h1⟩)]
        · push Not at h2
          rw [Set.indicator_of_mem (show t ∈ Iio (0 : ℝ) from h1), hzero t h2, zero_mul,
            Set.indicator_of_notMem (fun h => by linarith [h.1])]
      · rw [Set.indicator_of_notMem (show t ∉ Iio (0 : ℝ) from h1), zero_mul,
          Set.indicator_of_notMem (fun h => h1 h.2)]
    unfold defectLaplace
    rw [hind, integral_indicator measurableSet_Ioo]
    have hint : ‖∫ t in Ioo (-X') 0, phiStar G t * pairKernel (2 * t) τ‖ ≤
        (2 * CB * (1 + X') ^ N * 3) * X' := by
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (-X') 0)
        (C := 2 * CB * (1 + X') ^ N * 3) (f := fun t => phiStar G t * pairKernel (2 * t) τ)
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) (fun t ht => by
          rw [norm_mul, ← phiG_sub_gG]
          have hp := hpoly t
          have hta : |t| ≤ X' := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
          have hpow : (1 + |t|) ^ N ≤ (1 + X') ^ N :=
            pow_le_pow_left₀ (by positivity) (by linarith) N
          have h1 : ‖phiG G t - gG G t‖ ≤ 2 * CB * (1 + X') ^ N := by
            refine (norm_sub_le _ _).trans ?_
            nlinarith [hp.1, hp.2]
          exact mul_le_mul h1 (norm_pairKernel_two_mul_le_three t hτre hτ1) (norm_nonneg _)
            (by positivity))
      rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)] at h
      simpa using h
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hK₀]
    gcongr
  have hlim0 : Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace ((Iio (0 : ℝ)).indicator (phiStar G))
      ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (?_ : Tendsto (fun ε : ℝ => ε * K₀) (𝓝[>] 0) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with ε hε using hbound ε hε
    · have h : Tendsto (fun ε : ℝ => ε * K₀) (𝓝 0) (𝓝 (0 * K₀)) :=
        (continuous_id.mul continuous_const).tendsto (0 : ℝ)
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
  have h := tendsto_nhds_unique hrefl hlim0
  have : betaG G = 0 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
    rwa [div_eq_zero_iff, or_iff_left hπ] at h
  exact hβ this

/-! ### Linear growth of a monotone function -/

/-- **Almost-everywhere local growth integrates.**  If a monotone `C` satisfies
`C(y') − C(y) ≥ c(y' − y)` near almost every point of `(A, B)`, then `C(B + 1) − C(A) ≥ c(B − A)`. -/
theorem growth_of_ae_local_growth {C : ℝ → ℝ} (hC : Monotone C) {c A B : ℝ} (hc : 0 ≤ c)
    (hAB : A ≤ B)
    (hloc : ∀ᵐ x ∂(volume.restrict (Ioo A B)), ∃ δ : ℝ, 0 < δ ∧ ∀ y y' : ℝ, x - δ < y → y ≤ y' →
      y' < x + δ → c * (y' - y) ≤ C y' - C y) :
    c * (B - A) ≤ C (B + 1) - C A := by
  set μ := hC.stieltjesFunction.measure with hμ
  have hge : ∀ᵐ x ∂(volume.restrict (Ioo A B)), ENNReal.ofReal c ≤ μ.rnDeriv volume x := by
    filter_upwards [hloc, ae_restrict_of_ae hC.ae_hasDerivAt,
      ae_restrict_of_ae (Measure.rnDeriv_lt_top μ volume)] with x hx hd hfin
    obtain ⟨δ, hδ, hgrow⟩ := hx
    have hslope : Tendsto (slope C x) (𝓝[>] x) (𝓝 (μ.rnDeriv volume x).toReal) :=
      (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
        (nhdsWithin_mono _ fun y (hy : x < y) => ne_of_gt hy)
    have hcd : c ≤ (μ.rnDeriv volume x).toReal := by
      refine ge_of_tendsto hslope ?_
      filter_upwards [Ioo_mem_nhdsGT (show x < x + δ by linarith)] with y hy
      rw [slope_def_field, le_div_iff₀ (by linarith [hy.1])]
      exact hgrow x y (by linarith) hy.1.le hy.2
    rw [← ENNReal.ofReal_toReal hfin.ne]
    exact ENNReal.ofReal_le_ofReal hcd
  have h1 : ENNReal.ofReal c * ENNReal.ofReal (B - A) ≤ μ (Ioc A B) := by
    calc ENNReal.ofReal c * ENNReal.ofReal (B - A) = ∫⁻ x in Ioo A B, ENNReal.ofReal c := by
          rw [setLIntegral_const, Real.volume_Ioo]
      _ ≤ ∫⁻ x in Ioo A B, μ.rnDeriv volume x := lintegral_mono_ae hge
      _ ≤ ∫⁻ x in Ioc A B, μ.rnDeriv volume x := lintegral_mono_set Ioo_subset_Ioc_self
      _ = (volume.withDensity (μ.rnDeriv volume)) (Ioc A B) :=
          (withDensity_apply _ measurableSet_Ioc).symm
      _ ≤ μ (Ioc A B) := Measure.withDensity_rnDeriv_le μ volume _
  rw [hμ, StieltjesFunction.measure_Ioc, ← ENNReal.ofReal_mul hc, hC.stieltjesFunction_eq,
    hC.stieltjesFunction_eq] at h1
  have hB : Function.rightLim C B ≤ C (B + 1) := hC.rightLim_le (by linarith)
  have hA : C A ≤ Function.rightLim C A := hC.le_rightLim le_rfl
  rcases (ENNReal.ofReal_le_ofReal_iff' ).mp h1 with h | h
  · linarith
  · have : C A ≤ C (B + 1) := hC (by linarith)
    linarith


/-- A monotone function of power growth `α < 1` is eventually below every line of positive slope. -/
theorem eventually_sublinear_lt {C : ℝ → ℝ} {α K : ℝ} (hα1 : α < 1)
    (hCK : ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α) {c : ℝ} (hc : 0 < c) (A : ℝ) :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → C y < c * (y - 1 - A) + C A := by
  set α' : ℝ := max α 0 with hα'
  have hα'1 : α' < 1 := max_lt hα1 (by norm_num)
  set K' : ℝ := |K| with hK'
  have hev : ∀ᶠ y : ℝ in atTop, (2 * K' + 1) / c ≤ y ^ (1 - α') :=
    (tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hev
  refine ⟨max (max Y₀ 1) (2 * (c * (1 + A) - C A) / c + 1), fun y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hy)
  have hyY : Y₀ ≤ y := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hy)
  have hy2 : 2 * (c * (1 + A) - C A) / c + 1 ≤ y := le_trans (le_max_right _ _) hy
  have hy0 : 0 < y := by linarith
  have h1 : K * y ^ α ≤ K' * y ^ α' := by
    have hp : y ^ α ≤ y ^ α' := Real.rpow_le_rpow_of_exponent_le hy1 (le_max_left _ _)
    have h0 : 0 ≤ y ^ α := Real.rpow_nonneg hy0.le _
    calc K * y ^ α ≤ K' * y ^ α := mul_le_mul_of_nonneg_right (le_abs_self K) h0
      _ ≤ K' * y ^ α' := mul_le_mul_of_nonneg_left hp (abs_nonneg K)
  have hsplit : y ^ α' * y ^ (1 - α') = y := by
    rw [← Real.rpow_add hy0]; simp
  have h2 : (2 * K' + 1) * y ^ α' ≤ c * y := by
    have h := hY₀ y hyY
    rw [div_le_iff₀ hc] at h
    have h0 : 0 ≤ y ^ α' := Real.rpow_nonneg hy0.le _
    calc (2 * K' + 1) * y ^ α' ≤ (y ^ (1 - α') * c) * y ^ α' := mul_le_mul_of_nonneg_right h h0
      _ = c * (y ^ α' * y ^ (1 - α')) := by ring
      _ = c * y := by rw [hsplit]
  have h3 : K' * y ^ α' ≤ c / 2 * y := by
    have h0 : 0 ≤ y ^ α' := Real.rpow_nonneg hy0.le _
    nlinarith [abs_nonneg K]
  have h4 : c / 2 * y > c * (1 + A) - C A := by
    have := hy2
    rw [div_add_one hc.ne', div_le_iff₀ hc] at this
    nlinarith
  have := hCK y hy1
  linarith

/-! ### The theorems -/

/-- **Positivity forbids a decreasing linear lock phase.**  Let `G` be a Herglotz producer for the
weights `lam`.  Suppose that on the lower critical line
`G(1 − s) = κ₀ e^{iη(−τ)} e^{iβ₀C(−τ)} G(s)`, `s = ½ + 2iτ`, `τ < 0`,
where `C` is monotone and `C(x) ≤ K x^α` for `x ≥ 1`, for some `α < 1`.  Then `η ≥ 0`. -/
theorem linear_twist_slope_nonneg {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Monotone C)
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α)
    {κ₀ : ℂ} {η β₀ : ℝ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      κ₀ * cexp (((η * (-τ) : ℝ) : ℂ) * I) * cexp (((β₀ * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ)) :
    0 ≤ η := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  by_contra hη
  push Not at hη
  have hG20 : G 2 ≠ 0 := G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (2 : ℂ).re)
  obtain ⟨P, hP, hPG⟩ := exists_log_producer hΦd hGd
  have hlock' : ∀ x : ℝ, 0 < x → G (1 - vpt (1 / 2) x) =
      κ₀ * cexp (((η * x : ℝ) : ℂ) * I) * cexp (((β₀ * C x : ℝ) : ℂ) * I) * G (vpt (1 / 2) x) := by
    intro x hx
    have h := hlock (-x) (by linarith)
    rwa [neg_neg, lineS_neg_eq_vpt] at h
  obtain ⟨A, -, hA0, hGA⟩ := exists_ne_zero_beyond hsl hΦd hΦre hidT hGc hGd hG2 1
  obtain ⟨hβ, -⟩ := local_lock_growth hsl hΦre hidT hGc hGd hG2 hG20 hP hPG hC hη hlock' hA0 hGA
  set c : ℝ := -η / β₀ with hc
  have hc0 : 0 < c := div_pos (by linarith) hβ
  have hgrowB : ∀ B : ℝ, A ≤ B → G (vpt (1 / 2) B) ≠ 0 → c * (B - A) ≤ C (B + 1) - C A := by
    intro B hAB hGB
    refine growth_of_ae_local_growth hC hc0.le hAB ?_
    filter_upwards [ae_ne_zero_of_ends hΦd hΦre hGc hGd hG20 hP hPG hAB hGA hGB,
      ae_restrict_mem measurableSet_Ioo] with x hx hxT
    obtain ⟨-, δ, hδ, hloc⟩ := local_lock_growth hsl hΦre hidT hGc hGd hG2 hG20 hP hPG hC hη hlock'
      (x₀ := x) (by linarith [hxT.1]) hx
    refine ⟨δ, hδ, fun y y' h1 h2 h3 => ?_⟩
    have := hloc y y' h1 h2 h3
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ hβ]
    linarith
  obtain ⟨α, K, hα1, hCK⟩ := hgrowth
  obtain ⟨Y, hY⟩ := eventually_sublinear_lt hα1 hCK hc0 A
  obtain ⟨B, hB, hB0, hGB⟩ := exists_ne_zero_beyond hsl hΦd hΦre hidT hGc hGd hG2 (max A Y)
  have h1 := hgrowB B (le_trans (le_max_left _ _) hB) hGB
  have h2 := hY (B + 1) (by linarith [le_max_right A Y])
  have e : B + 1 - 1 - A = B - A := by ring
  rw [e] at h2
  linarith

/-- **Linear-twist rigidity.**  Let `G` be a Herglotz producer for the weights `lam`.  Suppose that
on the lower critical line `G(1 − s) = κ₀ e^{iη(−τ)} e^{iβ₀C(−τ)} G(s)`, `s = ½ + 2iτ`, `τ < 0`,
where `η` is real, `C` is monotone and `C(x) ≤ K x^α` for `x ≥ 1`, for some `α < 1`.  Then `η = 0`,
`lam(n) = Λ(n)` for all `n ≥ 2`, and RH holds. -/
theorem linear_twist_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Monotone C)
    (hgrowth : ∃ α K : ℝ, α < 1 ∧ ∀ x : ℝ, 1 ≤ x → C x ≤ K * x ^ α)
    {κ₀ : ℂ} {η β₀ : ℝ}
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      κ₀ * cexp (((η * (-τ) : ℝ) : ℂ) * I) * cexp (((β₀ * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ)) :
    η = 0 ∧ (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have h1 := linear_twist_slope_nonpos hsl hΦd hΦre hid hGc hGd hG2 hC hgrowth hlock
  have h2 := linear_twist_slope_nonneg hsl hΦd hΦre hid hGc hGd hG2 hC hgrowth hlock
  have hη : η = 0 := le_antisymm h1 h2
  refine ⟨hη, abelian_twist_power_rigidity hsl hΦd hΦre hid hGc hGd hG2 hC hgrowth
    (κ₀ := κ₀) (β₀ := β₀) fun τ hτ => ?_⟩
  rw [hlock τ hτ, hη]
  simp

end

end AbelianTwist

end RHTower
