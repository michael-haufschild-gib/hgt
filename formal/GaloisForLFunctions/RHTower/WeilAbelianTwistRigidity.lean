import GaloisForLFunctions.RHTower.HamburgerAbelianTwistContour

/-!
# Abelian twist rigidity: a slowly winding reflection phase forces `Λ` and RH

Let `G` be continuous on `Re s ≥ ½` with `G' = ΦG`, where `Φ` is the Herglotz form of Weil
positivity for weights `lam`.  Suppose that on the lower critical line

`G(1 − s) = κ₀ e^{iβ₀ C(−Im s/2)} G(s)`,

with `C` monotone and `C(x) = o(√x)`: for every `γ > 0` there is `K` with `C(x) ≤ γ√x + K` for
`x ≥ 1`.

**Theorem** (`abelian_twist_rigidity`).  Then `lam(n) = Λ(n)` for every `n ≥ 2`, and RH holds.

`C` may tend to infinity.  The twist need not settle, and no mean-value bound for the producer zeta
function `F` is assumed.  `MonotoneTwistLock.phase_lock_rigidity_of_monotone_twist` is the special
case of a bounded `C`.

**Proof.**
* *Every `m` sees the same limit.*  By the reflected Laplace identity
  (`PhaseLockRigidity.tendsto_lower_reflected_radial`), `ε J(ε + im) → β/π` for every `m ≥ 1`,
  where `J` is Hamburger's Laplace transform of the reflected boundary value `w·F` on `t < 0` and
  `β = G(1)/2`.
* *Main term.*  On `t ≤ −1` write `F k = a(m) ρ_m + d`.  The density `ρ_m` is the resonant
  right-edge term `m^{−(3/2+2it)} k_τ(3/2 + 2it)`.  The remainder satisfies
  `‖ε∫_{t≤b} d‖ ≤ K ε^{1/2} e^{bδ}` (`AbelianTwist.exists_norm_radialError_le`).
* *Layer cake.*  `e^{iβ₀C(−t)} = e^{iβ₀C(1)} + ∫_{x > C(1)} iβ₀e^{iβ₀x} 1[x ≤ C(−t)] dx`.  The sets
  `{t ≤ −1 : x ≤ C(−t)}` are half-lines `t ≤ b_x` with `b_x ≤ −((x − K)/γ)²`
  (`norm_setIntegral_twist_le`).  So the twisted remainder is
  `≪ ε^{1/2}(1 + |β₀|((K − C(1))⁺ + γ√(π/δ)))`.  Since `ε/δ = ‖τ‖ ≤ m + 1`, it is `≪ ε^{1/2} + γ`,
  and it tends to zero.
* *Scaling.*  `m^{−s}k_{mτ}(s) = m^{−1}k_τ(s)`, so the twisted main term at `(m, ε)` equals `a(m)`
  times the twisted main term at `(1, ε/m)`.  Hence `a(m)·(2β) = 2β`, and `β ≠ 0` because `G` has
  no zero on `Re s > ½`.  So `a(m) = 1`, `F = ζ`, and `lam = Λ`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel

noncomputable section

/-! ### Sublevel sets of a monotone phase are half-lines -/

/-- For monotone `C`, the set `{t ≤ −1 : x ≤ C(−t)}` is a half-line up to a point: integration over
it is integration over `t ≤ b` for some `b ≤ −1`, or the set is empty. -/
theorem exists_halfLine_of_monotone {C : ℝ → ℝ} (hC : Monotone C) (x : ℝ) :
    (∀ t, t ≤ -1 → C (-t) < x) ∨
      ∃ b : ℝ, b ≤ -1 ∧ (∀ c : ℝ, (∀ t, t ≤ -1 → x ≤ C (-t) → t ≤ c) → b ≤ c) ∧
        ∀ g : ℝ → ℂ, ∫ t in Iic (-1 : ℝ), (if x ≤ C (-t) then g t else 0) = ∫ t in Iic b, g t := by
  set S : Set ℝ := {t | t ≤ -1 ∧ x ≤ C (-t)} with hS
  by_cases hne : S.Nonempty
  · right
    have hbdd : BddAbove S := ⟨-1, fun t ht => ht.1⟩
    set b := sSup S with hb
    have hb1 : b ≤ -1 := csSup_le hne fun t ht => ht.1
    have hmem : ∀ t, t ≤ -1 → x ≤ C (-t) → t ≤ b := fun t ht hx => le_csSup hbdd ⟨ht, hx⟩
    have hlow : ∀ t, t < b → t ∈ S := by
      intro t ht
      obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hne ht
      exact ⟨by linarith [hs.1], hs.2.trans (hC (by linarith))⟩
    have hub : ∀ c : ℝ, (∀ t, t ≤ -1 → x ≤ C (-t) → t ≤ c) → b ≤ c :=
      fun c hc => csSup_le hne fun t ht => hc t ht.1 ht.2
    refine ⟨b, hb1, hub, fun g => ?_⟩
    have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Iic (-1 : ℝ) →
        (if x ≤ C (-t) then g t else 0) = (Iic b).indicator g t := by
      have hne_b : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by rw [ae_iff]; simp
      filter_upwards [hne_b] with t htb' ht
      by_cases hx : x ≤ C (-t)
      · rw [if_pos hx, Set.indicator_of_mem (show t ∈ Iic b from hmem t ht hx)]
      · rw [if_neg hx]
        by_cases htb : t ≤ b
        · exact absurd (hlow t (lt_of_le_of_ne htb htb')).2 hx
        · rw [Set.indicator_of_notMem (show t ∉ Iic b from htb)]
    rw [setIntegral_congr_ae measurableSet_Iic hae, setIntegral_indicator measurableSet_Iic,
      Set.inter_eq_right.mpr (Iic_subset_Iic.mpr hb1)]
  · left
    intro t ht
    by_contra h
    push Not at h
    exact hne ⟨t, ht, h⟩

/-! ### The twisted half-line integral -/

/-- The layer density `ψ(x) = iβ₀ e^{iβ₀x}` of the phase `e^{iβ₀x}`. -/
def phaseDensity (β₀ x : ℝ) : ℂ := (β₀ : ℂ) * I * cexp (((β₀ * x : ℝ) : ℂ) * I)

theorem norm_phaseDensity (β₀ x : ℝ) : ‖phaseDensity β₀ x‖ = |β₀| := by
  unfold phaseDensity
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs]; ring

theorem continuous_phaseDensity (β₀ : ℝ) : Continuous (phaseDensity β₀) := by
  unfold phaseDensity; fun_prop

theorem phase_eq_add_setIntegral (β₀ : ℝ) {u v : ℝ} (huv : u ≤ v) :
    cexp (((β₀ * v : ℝ) : ℂ) * I) = cexp (((β₀ * u : ℝ) : ℂ) * I) +
      ∫ x in Ioi u, (if x ≤ v then phaseDensity β₀ x else 0) := by
  have hd : ∀ x ∈ Set.uIcc u v, HasDerivAt (fun x : ℝ => cexp (((β₀ * x : ℝ) : ℂ) * I))
      (phaseDensity β₀ x) x := by
    intro x _
    have h1 : HasDerivAt (fun z : ℂ => cexp ((β₀ : ℂ) * I * z)) (cexp ((β₀ : ℂ) * I * x) *
        ((β₀ : ℂ) * I * 1)) (x : ℂ) := ((hasDerivAt_id (x : ℂ)).const_mul ((β₀ : ℂ) * I)).cexp
    have h2 := h1.comp_ofReal
    unfold phaseDensity
    convert h2 using 1
    · funext y; congr 1; push_cast; ring
    · push_cast; ring_nf
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_phaseDensity β₀).intervalIntegrable _ _)
  have hset : ∫ x in Ioi u, (if x ≤ v then phaseDensity β₀ x else 0) =
      ∫ x in u..v, phaseDensity β₀ x := by
    rw [intervalIntegral.integral_of_le huv]
    have e : (fun x => if x ≤ v then phaseDensity β₀ x else 0) = (Iic v).indicator (phaseDensity β₀) := by
      funext x; simp [Set.indicator_apply]
    rw [e, setIntegral_indicator measurableSet_Iic]
    congr 1
  rw [hset, hftc]; ring

/-- **The layer cake, general profile.**  Let `C` be monotone and let `d` satisfy
`‖∫_{t ≤ b} d‖ ≤ E e^{bδ}` for all `b ≤ −1`.  Let `Ψ` be the primitive of a measurable density `ψ`
with `‖ψ‖ ≤ L`: `Ψ(v) = Ψ(u) + ∫_{u < x ≤ v} ψ` for `u ≤ v`.  Let `φ ≥ 0` dominate `e^{bδ}` at every
level `x` whose superlevel set `{t ≤ −1 : x ≤ C(−t)}` lies in `t ≤ b`.  Then
`‖∫_{t ≤ −1} Ψ(C(−t)) d(t) dt‖ ≤ E(‖Ψ(C(1))‖ + L ∫_{x > C(1)} φ)`. -/
theorem norm_setIntegral_layer_le_of_profile {d : ℝ → ℂ} {C : ℝ → ℝ} (hC : Monotone C)
    {Ψ ψ : ℝ → ℂ} {L E δ Iφ : ℝ} {φ : ℝ → ℝ} (hL : 0 ≤ L) (hψm : Measurable ψ)
    (hψL : ∀ x, ‖ψ x‖ ≤ L)
    (hΨ : ∀ u v : ℝ, u ≤ v → Ψ v = Ψ u + ∫ x in Ioi u, (if x ≤ v then ψ x else 0))
    (hE : 0 ≤ E) (hδ : 0 < δ)
    (hdm : AEStronglyMeasurable d volume) (hdint : IntegrableOn d (Iic (-1)))
    (hdom : IntegrableOn (fun t => (C (-t) - C 1) * ‖d t‖) (Iic (-1)))
    (herr : ∀ b, b ≤ -1 → ‖∫ t in Iic b, d t‖ ≤ E * Real.exp (b * δ))
    (hφ0 : ∀ x, 0 ≤ φ x)
    (hφ : ∀ x b : ℝ, b ≤ -1 → (∀ c : ℝ, (∀ t, t ≤ -1 → x ≤ C (-t) → t ≤ c) → b ≤ c) →
      Real.exp (b * δ) ≤ φ x)
    (hφint : IntegrableOn φ (Ioi (C 1))) (hφI : ∫ x in Ioi (C 1), φ x ≤ Iφ) :
    ‖∫ t in Iic (-1 : ℝ), Ψ (C (-t)) * d t‖ ≤ E * (‖Ψ (C 1)‖ + L * Iφ) := by
  set μt : Measure ℝ := volume.restrict (Iic (-1 : ℝ)) with hμt
  set μx : Measure ℝ := volume.restrict (Ioi (C 1)) with hμx
  set F : ℝ × ℝ → ℂ := fun p => if p.2 ≤ C (-p.1) then ψ p.2 * d p.1 else 0 with hF
  -- pointwise layer cake
  have hlayer : ∀ t, t ≤ -1 → Ψ (C (-t)) * d t = Ψ (C 1) * d t + ∫ x, F (t, x) ∂μx := by
    intro t ht
    have hC1 : C 1 ≤ C (-t) := hC (by linarith)
    rw [hΨ (C 1) (C (-t)) hC1, add_mul]
    congr 1
    rw [hμx, ← integral_mul_const]
    congr 1; funext x; simp only [hF]; split_ifs <;> simp
  -- measurability and integrability on the product
  have hSm : MeasurableSet {p : ℝ × ℝ | p.2 ≤ C (-p.1)} :=
    measurableSet_le measurable_snd ((hC.measurable.comp measurable_neg).comp measurable_fst)
  have hFm : AEStronglyMeasurable F (μt.prod μx) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => ψ p.2 * d p.1) (μt.prod μx) :=
      (hψm.comp measurable_snd).aestronglyMeasurable.mul (hdm.restrict.comp_fst)
    refine (h1.indicator hSm).congr (Eventually.of_forall fun p => ?_)
    simp only [hF, Set.indicator_apply, Set.mem_setOf_eq]
  have hind : ∀ t, t ≤ -1 → Integrable ((Iic (C (-t))).indicator fun _ : ℝ => L * ‖d t‖) μx := by
    intro t ht
    rw [integrable_indicator_iff measurableSet_Iic]
    refine integrableOn_const (hs := ?_)
    rw [hμx, Measure.restrict_apply measurableSet_Iic,
      show Iic (C (-t)) ∩ Ioi (C 1) = Ioc (C 1) (C (-t)) by ext; simp [and_comm]]
    exact measure_Ioc_lt_top.ne
  have hFpt : ∀ t x, ‖F (t, x)‖ ≤ (Iic (C (-t))).indicator (fun _ : ℝ => L * ‖d t‖) x := by
    intro t x
    simp only [hF, Set.indicator_apply, Set.mem_Iic]
    split_ifs
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hψL x) (norm_nonneg _)
    · simp
  have hFsec : ∀ t, t ≤ -1 → Integrable (fun x => F (t, x)) μx := by
    intro t ht
    refine (hind t ht).mono' ?_ (Eventually.of_forall fun x => hFpt t x)
    show AEStronglyMeasurable (fun x => if x ≤ C (-t) then ψ x * d t else 0) μx
    exact (Measurable.ite (measurableSet_le measurable_id measurable_const) (hψm.mul_const _)
      measurable_const).aestronglyMeasurable
  have hFx : ∀ t, t ≤ -1 → ∫ x, ‖F (t, x)‖ ∂μx ≤ L * ‖d t‖ * (C (-t) - C 1) := by
    intro t ht
    have hC1 : C 1 ≤ C (-t) := hC (by linarith)
    refine (integral_mono (hFsec t ht).norm (hind t ht) (fun x => hFpt t x)).trans (le_of_eq ?_)
    rw [hμx, setIntegral_indicator measurableSet_Iic, setIntegral_const, smul_eq_mul,
      show Ioi (C 1) ∩ Iic (C (-t)) = Ioc (C 1) (C (-t)) by ext; simp [and_comm],
      Real.volume_real_Ioc_of_le hC1]
    ring
  have hFint : Integrable F (μt.prod μx) := by
    rw [integrable_prod_iff hFm]
    refine ⟨(ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall hFsec), ?_⟩
    refine (hdom.const_mul L).mono' hFm.norm.integral_prod_right' ?_
    refine (ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    have := hFx t ht
    linarith
  -- the layer-cake identity
  have hsplit : ∫ t in Iic (-1 : ℝ), Ψ (C (-t)) * d t =
      Ψ (C 1) * (∫ t in Iic (-1 : ℝ), d t) + ∫ x, ∫ t, F (t, x) ∂μt ∂μx := by
    rw [setIntegral_congr_fun measurableSet_Iic (fun t ht => hlayer t ht),
      integral_add (hdint.const_mul _) hFint.integral_prod_left, integral_const_mul]
    congr 1
    exact integral_integral_swap (f := fun t x => F (t, x)) hFint
  -- the inner integrals
  have hinner : ∀ x, ‖∫ t, F (t, x) ∂μt‖ ≤ L * (E * φ x) := by
    intro x
    have e : ∫ t, F (t, x) ∂μt = ψ x * ∫ t in Iic (-1 : ℝ), (if x ≤ C (-t) then d t else 0) := by
      rw [hμt, ← integral_const_mul]
      congr 1; funext t; simp only [hF]; split_ifs <;> simp
    rw [e, norm_mul]
    refine mul_le_mul (hψL x) ?_ (norm_nonneg _) hL
    rcases exists_halfLine_of_monotone hC x with h | ⟨b, hb1, hub, hint⟩
    · have hz : ∫ t in Iic (-1 : ℝ), (if x ≤ C (-t) then d t else 0) = 0 := by
        rw [setIntegral_congr_fun measurableSet_Iic (fun t ht => by
          rw [if_neg (not_le.mpr (h t ht))]), integral_zero]
      rw [hz, norm_zero]
      exact mul_nonneg hE (hφ0 x)
    · rw [hint]
      exact (herr b hb1).trans (mul_le_mul_of_nonneg_left (hφ x b hb1 hub) hE)
  -- assemble
  rw [hsplit]
  have hx_int : Integrable (fun x => L * (E * φ x)) μx := (hφint.const_mul E).const_mul _
  have h2 : ‖∫ x, ∫ t, F (t, x) ∂μt ∂μx‖ ≤ L * (E * Iφ) := by
    refine (norm_integral_le_of_norm_le hx_int (Eventually.of_forall hinner)).trans ?_
    rw [integral_const_mul, integral_const_mul]
    gcongr
  have h1 : ‖Ψ (C 1) * ∫ t in Iic (-1 : ℝ), d t‖ ≤ ‖Ψ (C 1)‖ * E := by
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((herr (-1) le_rfl).trans ?_) (norm_nonneg _)
    have : Real.exp (-1 * δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  calc ‖Ψ (C 1) * (∫ t in Iic (-1 : ℝ), d t) + ∫ x, ∫ t, F (t, x) ∂μt ∂μx‖
      ≤ ‖Ψ (C 1)‖ * E + L * (E * Iφ) := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = E * (‖Ψ (C 1)‖ + L * Iφ) := by ring

/-- **The twisted half-line integral, profile form.**  Let `C` be monotone and let `d` satisfy
`‖∫_{t ≤ b} d‖ ≤ E e^{bδ}` for all `b ≤ −1`.  Let `φ ≥ 0` dominate `e^{bδ}` at every level `x` whose
superlevel set `{t ≤ −1 : x ≤ C(−t)}` lies in `t ≤ b`.  Then
`‖∫_{t ≤ −1} e^{iβ₀C(−t)} d(t) dt‖ ≤ E(1 + |β₀| ∫_{x > C(1)} φ)`. -/
theorem norm_setIntegral_twist_le_of_profile {d : ℝ → ℂ} {C : ℝ → ℝ} (hC : Monotone C)
    {β₀ E δ Iφ : ℝ} {φ : ℝ → ℝ} (hE : 0 ≤ E) (hδ : 0 < δ)
    (hdm : AEStronglyMeasurable d volume) (hdint : IntegrableOn d (Iic (-1)))
    (hdom : IntegrableOn (fun t => (C (-t) - C 1) * ‖d t‖) (Iic (-1)))
    (herr : ∀ b, b ≤ -1 → ‖∫ t in Iic b, d t‖ ≤ E * Real.exp (b * δ))
    (hφ0 : ∀ x, 0 ≤ φ x)
    (hφ : ∀ x b : ℝ, b ≤ -1 → (∀ c : ℝ, (∀ t, t ≤ -1 → x ≤ C (-t) → t ≤ c) → b ≤ c) →
      Real.exp (b * δ) ≤ φ x)
    (hφint : IntegrableOn φ (Ioi (C 1))) (hφI : ∫ x in Ioi (C 1), φ x ≤ Iφ) :
    ‖∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * d t‖ ≤ E * (1 + |β₀| * Iφ) := by
  have h := norm_setIntegral_layer_le_of_profile hC (Ψ := fun v => cexp (((β₀ * v : ℝ) : ℂ) * I))
    (ψ := phaseDensity β₀) (abs_nonneg β₀) (continuous_phaseDensity β₀).measurable
    (fun x => (norm_phaseDensity β₀ x).le) (fun u v huv => phase_eq_add_setIntegral β₀ huv)
    hE hδ hdm hdint hdom herr hφ0 hφ hφint hφI
  rwa [Complex.norm_exp_ofReal_mul_I] at h

/-- **The twisted half-line integral.**  Let `C` be monotone with `C(x) ≤ γ√x + K` for `x ≥ 1`, and
let `d` satisfy `‖∫_{t ≤ b} d‖ ≤ E e^{bδ}` for all `b ≤ −1`.  Then
`‖∫_{t ≤ −1} e^{iβ₀C(−t)} d(t) dt‖ ≤ E(1 + |β₀|((K − C(1))⁺ + γ√(π/δ)))`. -/
theorem norm_setIntegral_twist_le {d : ℝ → ℂ} {C : ℝ → ℝ} (hC : Monotone C) {β₀ E δ γ K : ℝ}
    (hδ : 0 < δ) (hγ : 0 < γ) (hE : 0 ≤ E)
    (hgrowth : ∀ x : ℝ, 1 ≤ x → C x ≤ γ * Real.sqrt x + K)
    (hdm : AEStronglyMeasurable d volume) (hdint : IntegrableOn d (Iic (-1)))
    (hdom : IntegrableOn (fun t => (C (-t) - C 1) * ‖d t‖) (Iic (-1)))
    (herr : ∀ b, b ≤ -1 → ‖∫ t in Iic b, d t‖ ≤ E * Real.exp (b * δ)) :
    ‖∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * d t‖ ≤
      E * (1 + |β₀| * (max 0 (K - C 1) + γ * Real.sqrt (Real.pi / δ))) := by
  have hpi := Real.pi_pos
  set φ : ℝ → ℝ := fun x => (Iic K).indicator (fun _ => (1 : ℝ)) x +
    Real.exp (-(δ / γ ^ 2) * (x - K) ^ 2) with hφ
  have hφ1 : ∀ x, 0 ≤ (Iic K).indicator (fun _ => (1 : ℝ)) x :=
    fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => add_nonneg (hφ1 x) (Real.exp_pos _).le
  have hφb : ∀ x b : ℝ, b ≤ -1 → (∀ c : ℝ, (∀ t, t ≤ -1 → x ≤ C (-t) → t ≤ c) → b ≤ c) →
      Real.exp (b * δ) ≤ φ x := by
    intro x b hb1 hub
    by_cases hxK : x ≤ K
    · have : (Iic K).indicator (fun _ => (1 : ℝ)) x = 1 :=
        Set.indicator_of_mem (show x ∈ Iic K from hxK) _
      have hexp : Real.exp (b * δ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      simp only [hφ]; rw [this]; linarith [Real.exp_pos (-(δ / γ ^ 2) * (x - K) ^ 2)]
    · push Not at hxK
      have hbK : b ≤ -((x - K) / γ) ^ 2 := by
        refine hub _ fun t ht hxt => ?_
        have h1 : x ≤ γ * Real.sqrt (-t) + K := hxt.trans (hgrowth (-t) (by linarith))
        have h2 : (x - K) / γ ≤ Real.sqrt (-t) := by
          rw [div_le_iff₀ hγ]; linarith
        have h3 : ((x - K) / γ) ^ 2 ≤ -t := by
          have h0 : 0 ≤ (x - K) / γ := div_nonneg (by linarith) hγ.le
          calc ((x - K) / γ) ^ 2 ≤ (Real.sqrt (-t)) ^ 2 := pow_le_pow_left₀ h0 h2 2
            _ = -t := Real.sq_sqrt (by linarith)
        linarith
      have hexp : Real.exp (b * δ) ≤ Real.exp (-(δ / γ ^ 2) * (x - K) ^ 2) := by
        apply Real.exp_le_exp.mpr
        have : b * δ ≤ -((x - K) / γ) ^ 2 * δ := mul_le_mul_of_nonneg_right hbK hδ.le
        have e2 : -((x - K) / γ) ^ 2 * δ = -(δ / γ ^ 2) * (x - K) ^ 2 := by field_simp
        linarith
      simp only [hφ]; linarith [hφ1 x]
  set μx : Measure ℝ := volume.restrict (Ioi (C 1)) with hμx
  -- integrability of the bound and its integral
  have hgauss : Integrable (fun x : ℝ => Real.exp (-(δ / γ ^ 2) * (x - K) ^ 2)) := by
    have h := (integrable_exp_neg_mul_sq (b := δ / γ ^ 2) (by positivity)).comp_sub_right K
    exact h
  have hφint : Integrable φ μx := by
    refine Integrable.add ?_ hgauss.restrict
    rw [integrable_indicator_iff measurableSet_Iic]
    refine integrableOn_const (hs := ?_)
    rw [hμx, Measure.restrict_apply measurableSet_Iic,
      show Iic K ∩ Ioi (C 1) = Ioc (C 1) K by ext; simp [and_comm]]
    exact measure_Ioc_lt_top.ne
  have hφint_le : ∫ x, φ x ∂μx ≤ max 0 (K - C 1) + γ * Real.sqrt (Real.pi / δ) := by
    have hind : ∫ x, (Iic K).indicator (fun _ => (1 : ℝ)) x ∂μx = max 0 (K - C 1) := by
      rw [integral_indicator measurableSet_Iic, setIntegral_const, smul_eq_mul, mul_one, hμx,
        measureReal_restrict_apply measurableSet_Iic,
        show Iic K ∩ Ioi (C 1) = Ioc (C 1) K by ext; simp [and_comm], Real.volume_real_Ioc,
        max_comm]
    have hg : ∫ x, Real.exp (-(δ / γ ^ 2) * (x - K) ^ 2) ∂μx ≤ γ * Real.sqrt (Real.pi / δ) := by
      refine (setIntegral_le_integral hgauss (Eventually.of_forall fun x => (Real.exp_pos _).le)).trans
        (le_of_eq ?_)
      rw [integral_sub_right_eq_self (fun x => Real.exp (-(δ / γ ^ 2) * x ^ 2)) K,
        integral_gaussian]
      have e : Real.pi / (δ / γ ^ 2) = γ ^ 2 * (Real.pi / δ) := by field_simp
      rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hγ.le]
    have hint1 : Integrable ((Iic K).indicator fun _ => (1 : ℝ)) μx := by
      rw [integrable_indicator_iff measurableSet_Iic]
      refine integrableOn_const (hs := ?_)
      rw [hμx, Measure.restrict_apply measurableSet_Iic,
        show Iic K ∩ Ioi (C 1) = Ioc (C 1) K by ext; simp [and_comm]]
      exact measure_Ioc_lt_top.ne
    simp only [hφ]
    rw [integral_add hint1 hgauss.restrict, hind]
    linarith
  exact norm_setIntegral_twist_le_of_profile hC hE hδ hdm hdint hdom herr hφ0 hφb hφint hφint_le

/-! ### Bounds for the main density and the radial integrand -/

theorem continuous_rhoMain {m : ℕ} (hm : 1 ≤ m) {τ : ℂ} (hτ0 : τ ≠ 0) :
    Continuous (rhoMain m τ) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  unfold rhoMain
  refine Continuous.mul (Continuous.const_cpow (by fun_prop) (Or.inl hm0)) ?_
  have e : (fun t : ℝ => offKernel τ (((3 / 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)) =
      (fun y => offKernel τ (edgePt y)) ∘ fun t : ℝ => 2 * t := by
    funext t; simp only [Function.comp, edgePt]
  rw [e]
  exact (continuous_offKernel_edgePt hτ0).comp (continuous_const.mul continuous_id)

theorem norm_rhoMain_le {m : ℕ} (hm : 1 ≤ m) {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {t : ℝ}
    (ht : t ≤ -1) :
    ‖rhoMain m τ t‖ ≤ 4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ *
      Real.exp (-(2 * (τ.re / ‖τ‖) * |t|)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold rhoMain
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
  have hre : (-(((3 / 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re = -(3 / 2) := by simp
  rw [hre]
  have hmpow : (m : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num)
  have h2t : 1 ≤ |2 * t| := by rw [abs_mul, abs_two, abs_of_neg (by linarith : t < 0)]; linarith
  have hk := norm_offKernel_le hτre hτ1 (x := 3 / 2) (y := 2 * t) (by norm_num) (by norm_num) h2t
  have e : |2 * t| * (τ.re / ‖τ‖) = 2 * (τ.re / ‖τ‖) * |t| := by rw [abs_mul, abs_two]; ring
  rw [e] at hk
  calc (m : ℝ) ^ (-(3 / 2 : ℝ)) * ‖offKernel τ (((3 / 2 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖
      ≤ 1 * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(2 * (τ.re / ‖τ‖) * |t|))) :=
        mul_le_mul hmpow hk (norm_nonneg _) zero_le_one
    _ = _ := one_mul _


theorem integrableOn_rhoMain {m : ℕ} (hm : 1 ≤ m) {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) :
    IntegrableOn (rhoMain m τ) (Iic (-1)) := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hτn : 0 < ‖τ‖ := by linarith
  have hδ : 0 < 2 * (τ.re / ‖τ‖) := by positivity
  have hdom := ((integrable_one_add_abs_pow_mul_exp hδ 0).const_mul
    (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖)).integrableOn (s := Iic (-1))
  refine hdom.mono' (continuous_rhoMain hm hτ0).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Iic).mpr (Eventually.of_forall fun t ht => ?_))
  rw [pow_zero, one_mul]
  exact norm_rhoMain_le hm hτre hτ1 ht

/-! ### The twisted remainder -/

/-- The remainder density `d(t) = F(½ + 2it) k(2t, τ) − a_m ρ_m(τ, t)`. -/
def remainder (G : ℂ → ℂ) (am : ℂ) (m : ℕ) (τ : ℂ) (t : ℝ) : ℂ :=
  phiG G t * pairKernel (2 * t) τ - am * rhoMain m τ t

theorem continuous_remainder {G : ℂ → ℂ} (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (am : ℂ) {m : ℕ} (hm : 1 ≤ m) {τ : ℂ} (hτ0 : τ ≠ 0) : Continuous (remainder G am m τ) :=
  ((continuous_phiG hGc).mul (continuous_pairKernel_two_mul hτ0)).sub
    (continuous_const.mul (continuous_rhoMain hm hτ0))

theorem norm_remainder_le {G : ℂ → ℂ} {CB : ℝ} {N : ℕ} (hCB : 0 ≤ CB)
    (hpoly : ∀ t : ℝ, ‖phiG G t‖ ≤ CB * (1 + |t|) ^ N) (am : ℂ) {m : ℕ} (hm : 1 ≤ m) {τ : ℂ}
    (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {t : ℝ} (ht : t ≤ -1) :
    ‖remainder G am m τ t‖ ≤ (3 * CB + ‖am‖ * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖)) *
      ((1 + |t|) ^ N * Real.exp (-(2 * (τ.re / ‖τ‖) * |t|))) := by
  have hpow : 1 ≤ (1 + |t|) ^ N := one_le_pow₀ (by linarith [abs_nonneg t])
  have hτs : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by norm_num)
  have hk := norm_pairKernel_two_mul_le t hτre
  have hr := norm_rhoMain_le hm hτre hτ1 ht
  set E := Real.exp (-(2 * (τ.re / ‖τ‖) * |t|)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  unfold remainder
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 : ‖phiG G t‖ * ‖pairKernel (2 * t) τ‖ ≤ 3 * CB * ((1 + |t|) ^ N * E) := by
    calc ‖phiG G t‖ * ‖pairKernel (2 * t) τ‖
        ≤ (CB * (1 + |t|) ^ N) * (3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * E) :=
          mul_le_mul (hpoly t) hk (norm_nonneg _) (by positivity)
      _ ≤ (CB * (1 + |t|) ^ N) * (3 * 1 * E) := by gcongr
      _ = 3 * CB * ((1 + |t|) ^ N * E) := by ring
  have h2 : ‖am‖ * ‖rhoMain m τ t‖ ≤ ‖am‖ * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖) *
      ((1 + |t|) ^ N * E) := by
    calc ‖am‖ * ‖rhoMain m τ t‖ ≤ ‖am‖ * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * E) :=
          mul_le_mul_of_nonneg_left hr (norm_nonneg _)
      _ ≤ ‖am‖ * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * ((1 + |t|) ^ N * E)) := by
          gcongr; nlinarith
      _ = _ := by ring
  linarith

/-- The phase-weighted remainder is integrable on `t ≤ −1` when `C(x) ≤ K₁(x + 1)` for `x ≥ 1`. -/
theorem integrableOn_phase_mul_remainder {G : ℂ → ℂ} {CB : ℝ} {N : ℕ} (hCB : 0 ≤ CB)
    (hpoly : ∀ t : ℝ, ‖phiG G t‖ ≤ CB * (1 + |t|) ^ N)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s) {C : ℝ → ℝ} (hC : Monotone C) {K₁ : ℝ}
    (hK₁ : ∀ x : ℝ, 1 ≤ x → C x ≤ K₁ * (x + 1)) (am : ℂ) {m : ℕ} (hm : 1 ≤ m) {τ : ℂ}
    (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) (c : ℂ) :
    IntegrableOn (fun t => (C (-t) - C 1) * ‖c * remainder G am m τ t‖) (Iic (-1)) := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hτn : 0 < ‖τ‖ := by linarith
  have hδ : 0 < 2 * (τ.re / ‖τ‖) := by positivity
  set D := 3 * CB + ‖am‖ * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖) with hD
  have hD0 : 0 ≤ D := by positivity
  set A := 2 * |K₁| + |C 1| with hA
  have hdom := ((integrable_one_add_abs_pow_mul_exp hδ (N + 1)).const_mul
    (A * (‖c‖ * D))).integrableOn (s := Iic (-1))
  have hmeas : AEStronglyMeasurable (fun t => (C (-t) - C 1) * ‖c * remainder G am m τ t‖)
      (volume.restrict (Iic (-1))) :=
    (((hC.measurable.comp measurable_neg).sub_const _).mul
      (continuous_const.mul (continuous_remainder hGc am hm hτ0)).norm.measurable).aestronglyMeasurable
  refine hdom.mono' hmeas ((ae_restrict_iff' measurableSet_Iic).mpr
    (Eventually.of_forall fun t ht => ?_))
  have ht' : t ≤ -1 := ht
  have hC1 : C 1 ≤ C (-t) := hC (by linarith)
  have habs : |t| = -t := abs_of_neg (by linarith)
  have hCt : C (-t) - C 1 ≤ A * (1 + |t|) := by
    have h0 := hK₁ (-t) (by linarith)
    have h1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hk1 : K₁ * (-t + 1) ≤ |K₁| * (2 * (1 + |t|)) := by
      rw [habs]
      calc K₁ * (-t + 1) ≤ |K₁ * (-t + 1)| := le_abs_self _
        _ = |K₁| * (-t + 1) := by
            rw [abs_mul, abs_of_pos (show (0 : ℝ) < -t + 1 by linarith)]
        _ ≤ |K₁| * (2 * (1 + -t)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); linarith
    have hc1 := neg_abs_le (C 1)
    nlinarith [abs_nonneg K₁, abs_nonneg (C 1)]
  have hr := norm_remainder_le hCB hpoly am hm hτre hτ1 ht'
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) (norm_nonneg _)), norm_mul]
  set E := Real.exp (-(2 * (τ.re / ‖τ‖) * |t|))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  calc (C (-t) - C 1) * (‖c‖ * ‖remainder G am m τ t‖)
      ≤ (A * (1 + |t|)) * (‖c‖ * (D * ((1 + |t|) ^ N * E))) := by
        gcongr
    _ = A * (‖c‖ * D) * ((1 + |t|) ^ (N + 1) * E) := by ring


/-- **The twisted remainder vanishes radially.**  If `C` is monotone and `C(x) = o(√x)`, then
`ε ∫_{t ≤ −1} e^{iβ₀C(−t)} d(t) dt → 0` as `ε → 0⁺`, where `τ = ε + im` and `d` is the remainder
density. -/
theorem tendsto_twisted_remainder {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Monotone C)
    (hgrowth : ∀ γ : ℝ, 0 < γ → ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x → C x ≤ γ * Real.sqrt x + K)
    (β₀ : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
      remainder G (dirichletExp (lamLog lam) m) m ((ε : ℂ) + (m : ℂ) * I) t) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  set am := dirichletExp (lamLog lam) m with ham
  obtain ⟨K, hK⟩ := exists_norm_radialError_le hsl hΦre hid hGc hGd hG2 hm
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  obtain ⟨K₁, hK₁⟩ := hgrowth 1 one_pos
  have hK₁' : ∀ x : ℝ, 1 ≤ x → C x ≤ (1 + |K₁|) * (x + 1) := fun x hx => by
    have h := hK₁ x hx
    have hs : Real.sqrt x ≤ x := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    nlinarith [le_abs_self K₁, abs_nonneg K₁]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbound : ∀ γ : ℝ, 0 < γ → ∀ Kγ : ℝ, (∀ x : ℝ, 1 ≤ x → C x ≤ γ * Real.sqrt x + Kγ) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖(ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
        remainder G am m ((ε : ℂ) + (m : ℂ) * I) t‖ ≤
        |K| * (1 + |β₀| * max 0 (Kγ - C 1)) * ε ^ (1 / 2 : ℝ) +
          |K| * |β₀| * γ * Real.sqrt (Real.pi * (m + 1)) := by
    intro γ hγ Kγ hKγ ε hε hε1
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    have hτre : τ.re = ε := by simp [hτ]
    have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
    have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre0; simp at hτre0
    have hτ1 : 1 ≤ ‖τ‖ := by
      have h := Complex.abs_im_le_norm τ
      have him : τ.im = m := by simp [hτ]
      rw [him, abs_of_nonneg (Nat.cast_nonneg m)] at h; linarith
    have hτM : ‖τ‖ ≤ m + 1 := by
      have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
      rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
        Real.norm_eq_abs, abs_of_pos hε] at h
      linarith
    have hτpos : 0 < ‖τ‖ := by linarith
    set δ : ℝ := ε / ‖τ‖ with hδ
    have hδ0 : 0 < δ := div_pos hε hτpos
    set d : ℝ → ℂ := fun t => (ε : ℂ) * remainder G am m τ t with hd
    have hdc : Continuous d := continuous_const.mul (continuous_remainder hGc am hm hτ0)
    have hphik := MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2 hτre0
    have hrho := integrableOn_rhoMain hm hτre0 hτ1
    have hdint : IntegrableOn d (Iic (-1)) :=
      (hphik.integrableOn.sub (hrho.const_mul am)).const_mul (ε : ℂ)
    have hdom : IntegrableOn (fun t => (C (-t) - C 1) * ‖d t‖) (Iic (-1)) :=
      integrableOn_phase_mul_remainder hCB (fun t => (hpoly t).1) hGc hC hK₁' am hm hτre0 hτ1 _
    have herr : ∀ b, b ≤ -1 → ‖∫ t in Iic b, d t‖ ≤ (|K| * ε ^ (1 / 2 : ℝ)) * Real.exp (b * δ) := by
      intro b hb
      have h1 : ∫ t in Iic b, d t = (ε : ℂ) * ((∫ t in Iic b, phiG G t * pairKernel (2 * t) τ) -
          am * ∫ t in Iic b, rhoMain m τ t) := by
        simp only [hd, remainder]
        rw [integral_const_mul, integral_sub hphik.integrableOn
          ((hrho.mono_set (Iic_subset_Iic.mpr hb)).const_mul am), integral_const_mul]
      rw [h1]
      refine (hK ε hε hε1 b hb).trans ?_
      gcongr
      exact le_abs_self K
    have htw := norm_setIntegral_twist_le hC (β₀ := β₀) hδ0 hγ (by positivity) hKγ
      hdc.aestronglyMeasurable hdint hdom herr
    have e1 : (ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
        remainder G am m τ t = ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * d t := by
      rw [← integral_const_mul]; congr 1; funext t; simp only [hd]; ring
    rw [e1]
    refine htw.trans ?_
    have hsq : ε ^ (1 / 2 : ℝ) * Real.sqrt (Real.pi / δ) ≤ Real.sqrt (Real.pi * (m + 1)) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul hε.le]
      apply Real.sqrt_le_sqrt
      have e2 : ε * (Real.pi / δ) = Real.pi * ‖τ‖ := by
        rw [hδ]; field_simp
      rw [e2]; gcongr
    have hM0 : 0 ≤ max 0 (Kγ - C 1) := le_max_left _ _
    calc |K| * ε ^ (1 / 2 : ℝ) * (1 + |β₀| * (max 0 (Kγ - C 1) + γ * Real.sqrt (Real.pi / δ)))
        = |K| * (1 + |β₀| * max 0 (Kγ - C 1)) * ε ^ (1 / 2 : ℝ) +
            |K| * |β₀| * γ * (ε ^ (1 / 2 : ℝ) * Real.sqrt (Real.pi / δ)) := by ring
      _ ≤ |K| * (1 + |β₀| * max 0 (Kγ - C 1)) * ε ^ (1 / 2 : ℝ) +
            |K| * |β₀| * γ * Real.sqrt (Real.pi * (m + 1)) := by gcongr
  rw [Metric.tendsto_nhds]
  intro η hη
  set L : ℝ := |K| * |β₀| * Real.sqrt (Real.pi * (m + 1)) with hL
  have hL0 : 0 ≤ L := by positivity
  set γ : ℝ := η / (2 * (L + 1)) with hγ
  have hγ0 : 0 < γ := by positivity
  obtain ⟨Kγ, hKγ⟩ := hgrowth γ hγ0
  set A : ℝ := |K| * (1 + |β₀| * max 0 (Kγ - C 1)) with hA
  have hLγ : L * γ < η / 2 := by
    have e : L * γ = η / 2 * (L / (L + 1)) := by rw [hγ]; field_simp
    rw [e]
    exact mul_lt_of_lt_one_right (by positivity) ((div_lt_one (by positivity)).mpr (by linarith))
  have hsqrt : Tendsto (fun ε : ℝ => A * ε ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (1 / 2 : ℝ))) :=
      ((Real.continuous_rpow_const (q := 1 / 2) (by norm_num)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    rw [Real.zero_rpow (by norm_num)] at h
    simpa using h.const_mul A
  have hev1 := (tendsto_order.1 hsqrt).2 (η / 2) (by positivity)
  filter_upwards [hev1, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hεA hε
  rw [dist_zero_right]
  have h := hbound γ hγ0 Kγ hKγ ε hε.1 hε.2.le
  have e : |K| * |β₀| * γ * Real.sqrt (Real.pi * (m + 1)) = L * γ := by rw [hL]; ring
  rw [e] at h
  linarith


/-! ### Scaling of the main term -/

theorem measurable_phase (β₀ : ℝ) {C : ℝ → ℝ} (hC : Measurable C) :
    Measurable fun t : ℝ => cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) :=
  Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
    (measurable_const.mul (hC.comp measurable_neg))).mul_const _)

theorem integrableOn_phase_mul (β₀ : ℝ) {C : ℝ → ℝ} (hC : Measurable C) {f : ℝ → ℂ} {s : Set ℝ}
    (hf : IntegrableOn f s) :
    IntegrableOn (fun t => cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * f t) s := by
  refine hf.norm.mono' ((measurable_phase β₀ hC).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- The twisted main term `M(ε) = ε ∫_{t ≤ −1} e^{iβ₀C(−t)} ρ_1(ε + i, t) dt`. -/
def mainTwist (β₀ : ℝ) (C : ℝ → ℝ) (ε : ℝ) : ℂ :=
  (ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
    rhoMain 1 ((ε : ℂ) + ((1 : ℕ) : ℂ) * I) t

/-- **Scaling.**  Since `m^{−s}k_{mτ}(s) = m^{−1}k_τ(s)`, the twisted main term at `(m, ε)` is the
twisted main term at `(1, ε/m)`. -/
theorem mainTwist_scale (β₀ : ℝ) (C : ℝ → ℝ) {m : ℕ} (hm : 1 ≤ m) (ε : ℝ) :
    (ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
      rhoMain m ((ε : ℂ) + (m : ℂ) * I) t = mainTwist β₀ C (ε / m) := by
  unfold mainTwist
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  set τ' : ℂ := ((ε / m : ℝ) : ℂ) + ((1 : ℕ) : ℂ) * I with hτ'
  have hτ'0 : τ' ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [hτ'] at this
  have hτ : (ε : ℂ) + (m : ℂ) * I = (m : ℂ) * τ' := by
    rw [hτ']; push_cast; field_simp
  have hpt : ∀ t, rhoMain m ((ε : ℂ) + (m : ℂ) * I) t = (m : ℂ)⁻¹ * rhoMain 1 τ' t := by
    intro t
    unfold rhoMain
    rw [hτ, natCast_cpow_mul_offKernel_scale hm hτ'0]
    simp
  have e : (fun t => cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * rhoMain m ((ε : ℂ) + (m : ℂ) * I) t) =
      fun t => (m : ℂ)⁻¹ * (cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * rhoMain 1 τ' t) := by
    funext t; rw [hpt]; ring
  rw [e, integral_const_mul]
  push_cast
  ring

/-! ### The reflected limit lands on the main term -/

/-- The radial integral over `−1 < t < 0` is `O(ε)`. -/
theorem tendsto_near_piece {G : ℂ → ℂ} {CB : ℝ} {N : ℕ} (hCB : 0 ≤ CB)
    (hpoly : ∀ t : ℝ, ‖phiG G t‖ ≤ CB * (1 + |t|) ^ N) (β₀ : ℝ) (C : ℝ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0, cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
      (phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
  have hbd : ∀ ε : ℝ, 0 < ε → ‖(ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0,
      cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * (phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))‖ ≤
      (3 * CB * 2 ^ N) * ε := by
    intro ε hε
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    have hτre0 : 0 < τ.re := by simp [hτ]; exact hε
    have hτpos : 0 < ‖τ‖ := norm_pos_iff.mpr (by intro h; rw [h] at hτre0; simp at hτre0)
    have hI : ‖∫ t in Ioo (-1 : ℝ) 0, cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
        (phiG G t * pairKernel (2 * t) τ)‖ ≤ (3 * CB * 2 ^ N) * ‖τ‖ ^ (-(1 / 2 : ℝ)) := by
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (-1 : ℝ) 0)
        (f := fun t => cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * (phiG G t * pairKernel (2 * t) τ))
        (C := (3 * CB * 2 ^ N) * ‖τ‖ ^ (-(1 / 2 : ℝ))) measure_Ioo_lt_top (fun t ht => by
          rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
          have hab : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, by linarith [ht.2]⟩
          have hp : (1 + |t|) ^ N ≤ 2 ^ N :=
            pow_le_pow_left₀ (by positivity) (by linarith) N
          have hk := norm_pairKernel_two_mul_le t hτre0
          have hq : 0 ≤ τ.re / ‖τ‖ := by positivity
          have hexp : Real.exp (-(2 * (τ.re / ‖τ‖) * |t|)) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg t])
          calc ‖phiG G t‖ * ‖pairKernel (2 * t) τ‖
              ≤ (CB * (1 + |t|) ^ N) *
                  (3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(2 * (τ.re / ‖τ‖) * |t|))) :=
                mul_le_mul (hpoly t) hk (norm_nonneg _) (by positivity)
            _ ≤ (CB * 2 ^ N) * (3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * 1) := by gcongr
            _ = (3 * CB * 2 ^ N) * ‖τ‖ ^ (-(1 / 2 : ℝ)) := by ring)
      rw [Real.volume_real_Ioo_of_le (by norm_num)] at h
      simpa using h
    have hτs : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      have h1 : 1 ≤ ‖τ‖ := by
        have h := Complex.abs_im_le_norm τ
        have him : τ.im = m := by simp [hτ]
        rw [him, abs_of_nonneg (Nat.cast_nonneg m)] at h
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    calc ε * ‖_‖ ≤ ε * ((3 * CB * 2 ^ N) * 1) :=
          mul_le_mul_of_nonneg_left (hI.trans (by gcongr)) hε.le
      _ = _ := by ring
  have hlin : Tendsto (fun ε : ℝ => (3 * CB * 2 ^ N) * ε) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => (3 * CB * 2 ^ N) * ε) (𝓝 0) (𝓝 ((3 * CB * 2 ^ N) * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact squeeze_zero_norm' (eventually_nhdsWithin_of_forall fun ε hε => hbd ε hε) hlin


/-- **The reflected limit lands on the main term.**  Under the lock
`G(1 − s) = κ₀ e^{iβ₀C(−τ)} G(s)` on the lower line, with `C` monotone, if the twisted remainder
vanishes radially at `m ≥ 1`, then `κ₀ a(m) M(ε/m) → 2β`. -/
theorem tendsto_mainTwist_of_remainder {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Measurable C) {κ₀ : ℂ} {β₀ : ℝ}
    (hlock : ∀ τ : ℝ, τ < 0 →
      G (1 - lineS τ) = κ₀ * cexp (((β₀ * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ))
    {m : ℕ} (hm : 1 ≤ m)
    (hrem : Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ),
      cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
        remainder G (dirichletExp (lamLog lam) m) m ((ε : ℂ) + (m : ℂ) * I) t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => κ₀ * dirichletExp (lamLog lam) m * mainTwist β₀ C (ε / m)) (𝓝[>] 0)
      (𝓝 (2 * betaG G)) := by
  have hpi := Real.pi_pos
  set am := dirichletExp (lamLog lam) m with ham
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  have hrefl := tendsto_lower_reflected_radial hsl hΦre hid hGc hGd hG2 hm
  have hnear := tendsto_near_piece hCB (fun t => (hpoly t).1) β₀ C hm
  have hdecomp : ∀ ε : ℝ, 0 < ε →
      ((2 * Real.pi : ℝ) : ℂ) * ((ε : ℂ) * defectLaplace ((Iio (0 : ℝ)).indicator (phiStar G))
        ((ε : ℂ) + (m : ℂ) * I)) -
        κ₀ * ((ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
          remainder G am m ((ε : ℂ) + (m : ℂ) * I) t) -
        κ₀ * ((ε : ℂ) * ∫ t in Ioo (-1 : ℝ) 0, cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
          (phiG G t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))) =
      κ₀ * am * mainTwist β₀ C (ε / m) := by
    intro ε hε
    rw [← mainTwist_scale β₀ C hm ε]
    set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
    have hτre0 : 0 < τ.re := by simp [hτ]; exact hε
    have hτ1 : 1 ≤ ‖τ‖ := by
      have h := Complex.abs_im_le_norm τ
      have him : τ.im = m := by simp [hτ]
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rw [him, abs_of_nonneg (Nat.cast_nonneg m)] at h; linarith
    have hphik := MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2 hτre0
    have hrho := integrableOn_rhoMain hm hτre0 hτ1
    unfold defectLaplace
    have hind : (fun t => (Iio (0 : ℝ)).indicator (phiStar G) t * pairKernel (2 * t) τ) =
        (Iio (0 : ℝ)).indicator (fun t => phiStar G t * pairKernel (2 * t) τ) := by
      funext t
      by_cases ht : t ∈ Iio (0 : ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
    rw [hind, integral_indicator measurableSet_Iio]
    have hcongr : ∫ t in Iio (0 : ℝ), phiStar G t * pairKernel (2 * t) τ =
        ∫ t in Iio (0 : ℝ), κ₀ * (cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
          (phiG G t * pairKernel (2 * t) τ)) := by
      refine setIntegral_congr_fun measurableSet_Iio fun t ht => ?_
      have ht0 : t < 0 := ht
      simp only [phiStar, phiG]
      rw [hlock t ht0]
      ring
    have hsplit : Iio (0 : ℝ) = Iic (-1) ∪ Ioo (-1) 0 := by
      ext t
      simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
      constructor
      · intro h
        by_cases h1 : t ≤ -1
        · exact Or.inl h1
        · exact Or.inr ⟨by linarith, h⟩
      · rintro (h | h)
        · linarith
        · exact h.2
    have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioo (-1) 0) :=
      Set.disjoint_left.mpr fun t h1 h2 => by
        simp only [mem_Iic] at h1; simp only [mem_Ioo] at h2; linarith [h2.1]
    have hint1 := integrableOn_phase_mul β₀ hC (s := Iic (-1)) hphik.integrableOn
    have hint2 := integrableOn_phase_mul β₀ hC (s := Ioo (-1) 0) hphik.integrableOn
    have hint3 := integrableOn_phase_mul β₀ hC (s := Iic (-1))
      (f := remainder G am m τ) (hphik.integrableOn.sub (hrho.const_mul am))
    have hint4 := (integrableOn_phase_mul β₀ hC hrho).const_mul am
    rw [hcongr, integral_const_mul, hsplit, setIntegral_union hdisj measurableSet_Ioo hint1 hint2]
    have hfar : ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
        (phiG G t * pairKernel (2 * t) τ) =
        (∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * remainder G am m τ t) +
          am * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) * rhoMain m τ t := by
      rw [← integral_const_mul, ← integral_add hint3 hint4]
      refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
      simp only [remainder]; ring
    rw [hfar]
    have h2pi : ((2 * Real.pi : ℝ) : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 := by
      push_cast; field_simp
    linear_combination (↑ε * (κ₀ * ((∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
      remainder G am m τ t) + am * ∫ t in Iic (-1 : ℝ), cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
        rhoMain m τ t) + κ₀ * ∫ t in Ioo (-1 : ℝ) 0, cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
          (phiG G t * pairKernel (2 * t) τ))) * h2pi
  have hlim := (((hrefl.const_mul ((2 * Real.pi : ℝ) : ℂ)).sub (hrem.const_mul κ₀)).sub
    (hnear.const_mul κ₀))
  have hval : ((2 * Real.pi : ℝ) : ℂ) * (betaG G / (Real.pi : ℂ)) - κ₀ * 0 - κ₀ * 0 =
      2 * betaG G := by
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
    push_cast; field_simp; ring
  rw [hval] at hlim
  exact hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε => hdecomp ε hε)


/-- **The reflected limit lands on the main term**, for a monotone phase `C(x) = o(√x)`. -/
theorem tendsto_mainTwist {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Monotone C)
    (hgrowth : ∀ γ : ℝ, 0 < γ → ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x → C x ≤ γ * Real.sqrt x + K)
    {κ₀ : ℂ} {β₀ : ℝ}
    (hlock : ∀ τ : ℝ, τ < 0 →
      G (1 - lineS τ) = κ₀ * cexp (((β₀ * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ))
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => κ₀ * dirichletExp (lamLog lam) m * mainTwist β₀ C (ε / m)) (𝓝[>] 0)
      (𝓝 (2 * betaG G)) :=
  tendsto_mainTwist_of_remainder hsl hΦre hid hGc hGd hG2 hC.measurable hlock hm
    (tendsto_twisted_remainder hsl hΦre hid hGc hGd hG2 hC hgrowth β₀ hm)

/-! ### The coefficients and the conclusion -/

/-- If every Dirichlet coefficient of the producer zeta function `F = exp(Σ lam(n)n^{−s}/log n)` is
one, then `lam = Λ` and RH holds. -/
theorem vonMangoldt_and_RH_of_coeff_eq_one {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (hone : ∀ n : ℕ, n ≠ 0 → dirichletExp (lamLog lam) n = 1) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have hall : ∀ {n : ℕ}, n ≠ 0 → a n = (1 : ℕ → ℂ) n := fun hn => hone _ hn
  have hζ : ∀ s : ℂ, 1 < s.re → zetaOf lam s = riemannZeta s := by
    intro s hs
    rw [← (hLa s hs).2, LSeries_congr hall s, LSeries_one_eq_riemannZeta hs]
  have hLam : ∀ s : ℂ, 1 < s.re →
      LSeries (lamTwo lam) s = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    intro s hs
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : riemannZeta =ᶠ[𝓝 s] zetaOf lam := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact (hζ z hz).symm
    have hd := (hasDerivAt_zetaOf hsl hs).congr_of_eventuallyEq hev
    have hζne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, hd.deriv, hζ s hs]
    field_simp
  have habs1 : LSeries.abscissaOfAbsConv (lamTwo lam) < ⊤ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => lseriesSummable_of_le (norm_lamTwo_le lam) hsl (by simpa using hy))
      (EReal.coe_lt_top 1)
  have habs2 :
      LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < ⊤ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy))
      (EReal.coe_lt_top 1)
  have hEv : (fun x : ℝ => LSeries (lamTwo lam) x) =ᶠ[atTop]
      fun x : ℝ => LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact hLam x (by simpa using hx)
  refine ⟨fun n hn => ?_, ?_⟩
  · have h := LSeries.eq_of_LSeries_eventually_eq habs1 habs2 hEv (n := n) (by omega)
    simp only [lamTwo, if_pos hn] at h
    exact_mod_cast h
  · by_contra hRH
    obtain ⟨ρ, hρ0, hρ1, hρ2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
    set Z : ℂ → ℂ := fun s => s * (s - 1) * completedRiemannZeta₀ s + 1 with hZ
    have hZd : Differentiable ℂ Z := by
      have := differentiable_completedZeta₀
      intro s; simp only [hZ]; fun_prop
    set U : Set ℂ := {z : ℂ | 1 / 2 < z.re} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hZa : AnalyticOnNhd ℂ Z U := hZd.differentiableOn.analyticOnNhd hUo
    have hGa : AnalyticOnNhd ℂ G U := by
      have : DifferentiableOn ℂ G U := fun z hz =>
        (hGd z hz).differentiableAt.differentiableWithinAt
      exact this.analyticOnNhd hUo
    have hZΛ : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Z s = s * (s - 1) * completedRiemannZeta s := by
      intro s h0 h1
      have h1' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
      have h1'' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
      simp only [hZ]
      rw [completedRiemannZeta_eq]
      field_simp
      ring
    have hΛζ : ∀ s : ℂ, 0 < s.re → completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
      intro s hs
      have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
      rw [riemannZeta_def_of_ne_zero h0]
      field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hs]
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : G =ᶠ[𝓝 (2 : ℂ)] Z := by
      filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
      have hz' : 1 < z.re := hz
      have h0 : z ≠ 0 := by intro h; rw [h] at hz'; simp at hz'; linarith
      have h1 : z ≠ 1 := by intro h; rw [h] at hz'; simp at hz'
      rw [hZΛ z h0 h1, hΛζ z (by linarith), ← hζ z hz', G_eq_bigG hsl hid hGd hG2 hz']
      unfold bigG; ring
    have h2U : (2 : ℂ) ∈ U := by simp [hU]; norm_num
    have hglob := hGa.eqOn_of_preconnected_of_eventuallyEq hZa
      (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected h2U hev hρ1
    have hρne0 : ρ ≠ 0 := by intro h; rw [h] at hρ1; simp at hρ1; linarith
    have hρne1 : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
    have hzero : G ρ = 0 := by
      rw [hglob, hZΛ ρ hρne0 hρne1, hΛζ ρ (by linarith), hρ0, mul_zero, mul_zero]
    exact G_ne_zero hΦd hGd hG2 hρ1 hzero

/-- **Abelian twist rigidity from radial vanishing of the twisted remainder.**  Let `G` be a
Herglotz producer for `lam` with lower-line lock `G(1 − s) = κ₀ e^{iβ₀C(−τ)} G(s)`, `C` monotone.  If
for every `m ≥ 1` the twisted remainder `ε ∫_{t ≤ −1} e^{iβ₀C(−t)} d_m(t) dt` tends to zero, then
`lam(n) = Λ(n)` for all `n ≥ 2`, and RH holds. -/
theorem abelian_twist_rigidity_of_remainder {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Measurable C) {κ₀ : ℂ} {β₀ : ℝ}
    (hlock : ∀ τ : ℝ, τ < 0 →
      G (1 - lineS τ) = κ₀ * cexp (((β₀ * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ))
    (hrem : ∀ m : ℕ, 1 ≤ m → Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ),
      cexp (((β₀ * C (-t) : ℝ) : ℂ) * I) *
        remainder G (dirichletExp (lamLog lam) m) m ((ε : ℂ) + (m : ℂ) * I) t) (𝓝[>] 0) (𝓝 0)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hidT : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  set a := dirichletExp (lamLog lam) with ha_def
  have ha1 : a 1 = 1 := dirichletExp_one (lamLog_zero lam) (lamLog_one lam)
  have hβ : betaG G ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))
      two_ne_zero
  have h1 := tendsto_mainTwist_of_remainder hsl hΦre hidT hGc hGd hG2 hC hlock le_rfl
    (hrem 1 le_rfl)
  have h1' : Tendsto (fun ε => κ₀ * mainTwist β₀ C ε) (𝓝[>] 0) (𝓝 (2 * betaG G)) := by
    refine h1.congr fun ε => ?_
    rw [← ha_def, ha1, Nat.cast_one, div_one, mul_one]
  have hone : ∀ n : ℕ, n ≠ 0 → a n = 1 := by
    intro n hn
    have hm : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hm
    have hscale : Tendsto (fun ε : ℝ => ε / n) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h : Tendsto (fun ε : ℝ => ε / n) (𝓝 0) (𝓝 (0 / n)) :=
          (continuous_id.div_const _).tendsto 0
        rw [zero_div] at h
        exact h.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun ε hε => div_pos hε hn0
    have hA := (h1'.comp hscale).const_mul (a n)
    have hB := tendsto_mainTwist_of_remainder hsl hΦre hidT hGc hGd hG2 hC hlock hm (hrem n hm)
    have hB' : Tendsto (fun ε => a n * (κ₀ * mainTwist β₀ C (ε / n))) (𝓝[>] 0)
        (𝓝 (2 * betaG G)) := hB.congr fun ε => by rw [← ha_def]; ring
    have heq := tendsto_nhds_unique hA hB'
    exact mul_right_cancel₀ (mul_ne_zero two_ne_zero hβ) (heq.trans (one_mul _).symm)
  exact vonMangoldt_and_RH_of_coeff_eq_one hsl hΦd hidT hGd hG2 hone


/-- **Abelian twist rigidity.**  Let `G` be a Herglotz producer for the weights `lam`.  Suppose
that on the lower critical line `G(1 − s) = κ₀ e^{iβ₀C(−τ)} G(s)`, `s = ½ + 2iτ`, `τ < 0`, where
`C` is monotone and `C(x) = o(√x)`.  Then `lam(n) = Λ(n)` for all `n ≥ 2`, and RH holds. -/
theorem abelian_twist_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {C : ℝ → ℝ} (hC : Monotone C)
    (hgrowth : ∀ γ : ℝ, 0 < γ → ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x → C x ≤ γ * Real.sqrt x + K)
    {κ₀ : ℂ} {β₀ : ℝ}
    (hlock : ∀ τ : ℝ, τ < 0 →
      G (1 - lineS τ) = κ₀ * cexp (((β₀ * C (-τ) : ℝ) : ℂ) * I) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis :=
  abelian_twist_rigidity_of_remainder hsl hΦd hΦre hid hGc hGd hG2 hC.measurable hlock fun _ hm =>
    tendsto_twisted_remainder hsl hΦre hid hGc hGd hG2 hC hgrowth β₀ hm

end

end AbelianTwist

end RHTower
