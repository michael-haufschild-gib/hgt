/-
# The connected-symmetry barrier: no connected deformation group can mix deck charges

The deck charge of a window boundary lives in the discrete group `ZMod (2^k)`.  This file proves
that along ANY preconnected parameter space of deformations — the member and the window may both
move, only boundary nonvanishing is required — the charge is constant.  Consequences:

* `not_surjective_loopCharge_of_preconnected` — a connected symmetry group's orbit map can never
  surject onto the deck classes at a positive level: connectedness and class-surjectivity are
  jointly unsatisfiable.  Any "connected symmetry whose orbits realize all classes" is impossible,
  for every action and every window transport.
* the parameter space is arbitrary preconnected, NOT path-connected: the proof is an open–closed
  domination argument, so it covers solenoidal parameter groups (connected, not path-connected) —
  in particular the dyadic solenoid, the natural symmetry shape of the `2^k`-tower, cannot mix
  classes either.
* `boxCharge_conserved_moving` — conservation on the pair space: the box charge is invariant along
  deformations that move the member AND the window, extending the fixed-circle conservation to
  the full pair `(member, window)`.
* `boxCharge_eq_zero_of_vacuum` — a member nonvanishing on the closed window has charge zero: the
  boundary loop contracts radially through nonvanishing loops.
* `rh_iff_no_protected_defect` — the Riemann Hypothesis holds iff no hypothetical right-half
  ξ-defect is topologically protected: every isolating window pair around a right-half zero can be
  deformed, through boundary-nonvanishing pairs, to a vacuum pair.  Conservation makes the charge a
  path-component invariant of the pair space; a defect of order `m` joined to vacuum forces
  `2^k ∣ m` at every level, hence `m = 0`.
-/
import GaloisForLFunctions.RHTower.ChargeMotion
import GaloisForLFunctions.RHTower.IsolatingAnnulusRung
import GaloisForLFunctions.RHTower.RiemannTower

noncomputable section

namespace RHTower

open Complex Metric Set

/-! ### §1 Dominated loops wind identically -/

/-- **Dominated deformation.**  If the loop `δ` stays closer to the loop `γ` than the floor `m`
that `γ` keeps from zero, the straight-line homotopy between them never vanishes, so the winding
numbers agree. -/
theorem windingNumber_eq_of_close {γ δ : ℝ → ℂ} {a b m : ℝ}
    (hγc : Continuous γ) (hδc : Continuous δ)
    (hγloop : γ a = γ b) (hδloop : δ a = δ b)
    (hm : ∀ t, m ≤ ‖γ t‖) (hclose : ∀ t, ‖δ t - γ t‖ < m) :
    windingNumber δ a b = windingNumber γ a b := by
  set clamp : ℝ → ℝ := fun σ => min 1 (max 0 σ) with hclampdef
  have hclamp_cont : Continuous clamp := continuous_const.min (continuous_const.max continuous_id)
  have hcl0 : ∀ σ, 0 ≤ clamp σ := fun σ => le_min zero_le_one (le_max_left 0 σ)
  have hcl1 : ∀ σ, clamp σ ≤ 1 := fun σ => min_le_left _ _
  refine (windingNumber_of_homotopic (γ₀ := γ) (γ₁ := δ)
    (fun σ t => γ t + ↑(clamp σ) * (δ t - γ t)) ?_ ?_ ?_ ?_ ?_).symm
  · exact (hγc.comp continuous_snd).add
      ((Complex.continuous_ofReal.comp (hclamp_cont.comp continuous_fst)).mul
        ((hδc.comp continuous_snd).sub (hγc.comp continuous_snd)))
  · intro σ t h
    have h1 : γ t = -(((clamp σ : ℝ) : ℂ) * (δ t - γ t)) := eq_neg_of_add_eq_zero_left h
    have h2 : ‖γ t‖ ≤ ‖δ t - γ t‖ := by
      have hval : ‖γ t‖ = clamp σ * ‖δ t - γ t‖ := by
        conv_lhs => rw [h1]
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hcl0 σ)]
      rw [hval]
      exact mul_le_of_le_one_left (norm_nonneg _) (hcl1 σ)
    linarith [hm t, hclose t]
  · intro σ
    simp only [hγloop, hδloop]
  · intro t
    have hc0 : clamp 0 = 0 := by norm_num [hclampdef]
    show γ t + ↑(clamp 0) * (δ t - γ t) = γ t
    rw [hc0]
    simp
  · intro t
    have hc1 : clamp 1 = 1 := by norm_num [hclampdef]
    show γ t + ↑(clamp 1) * (δ t - γ t) = δ t
    rw [hc1]
    push_cast
    ring

/-! ### §2 Preconnected parameter spaces cannot mix winding numbers -/

/-- **The connected-parameter constancy law.**  Along ANY preconnected space of parameters — a
connected topological group of symmetries in particular — a jointly continuous family of
nonvanishing `2π`-periodic loops has constant winding number.  The proof is local domination plus
open–closed, NOT path lifting: it therefore covers connected parameter spaces with no nontrivial
paths at all, such as solenoids. -/
theorem windingNumber_const_of_preconnected {G : Type*} [TopologicalSpace G] [PreconnectedSpace G]
    (Φ : G → ℝ → ℂ) (hc : Continuous fun p : G × ℝ => Φ p.1 p.2)
    (hnv : ∀ g t, Φ g t ≠ 0) (hper : ∀ g, Function.Periodic (Φ g) (2 * Real.pi))
    (g₀ g₁ : G) :
    windingNumber (Φ g₀) 0 (2 * Real.pi) = windingNumber (Φ g₁) 0 (2 * Real.pi) := by
  have hev : ∀ g₀ : G, ∀ᶠ g in nhds g₀,
      windingNumber (Φ g) 0 (2 * Real.pi) = windingNumber (Φ g₀) 0 (2 * Real.pi) := by
    intro h₀
    have hΦc : ∀ g : G, Continuous (Φ g) := fun g =>
      hc.comp (continuous_const.prodMk continuous_id)
    -- the base loop keeps a positive floor from zero, attained on one period
    have hKne : (Icc (0:ℝ) (2 * Real.pi)).Nonempty :=
      nonempty_Icc.mpr (le_of_lt Real.two_pi_pos)
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hKne ((hΦc h₀).norm.continuousOn)
    have hm0 : 0 < ‖Φ h₀ t₀‖ := norm_pos_iff.mpr (hnv h₀ t₀)
    have hminOn := isMinOn_iff.mp hmin
    have hlow : ∀ t : ℝ, ‖Φ h₀ t₀‖ ≤ ‖Φ h₀ t‖ := by
      intro t
      obtain ⟨y, hy, hval⟩ := (hper h₀).exists_mem_Ico₀ Real.two_pi_pos t
      rw [hval]
      exact hminOn y (Ico_subset_Icc_self hy)
    -- uniform domination on a parameter neighbourhood: the tube lemma
    have hopen : IsOpen {p : G × ℝ | ‖Φ p.1 p.2 - Φ h₀ p.2‖ < ‖Φ h₀ t₀‖} := by
      have hcd : Continuous fun p : G × ℝ => ‖Φ p.1 p.2 - Φ h₀ p.2‖ :=
        (hc.sub (hc.comp (continuous_const.prodMk continuous_snd))).norm
      exact isOpen_lt hcd continuous_const
    have hsub : ({h₀} : Set G) ×ˢ Icc (0:ℝ) (2 * Real.pi) ⊆
        {p : G × ℝ | ‖Φ p.1 p.2 - Φ h₀ p.2‖ < ‖Φ h₀ t₀‖} := by
      rintro ⟨g, t⟩ ⟨hg, -⟩
      rw [mem_singleton_iff] at hg
      subst hg
      simpa using hm0
    obtain ⟨u, v, hu, -, hgu, hKv, huv⟩ :=
      generalized_tube_lemma isCompact_singleton isCompact_Icc hopen hsub
    filter_upwards [hu.mem_nhds (hgu rfl)] with g hg
    -- domination extends from one period to the line by periodicity of the difference
    have hdper : Function.Periodic (fun t => Φ g t - Φ h₀ t) (2 * Real.pi) := by
      intro t
      show Φ g (t + 2 * Real.pi) - Φ h₀ (t + 2 * Real.pi) = Φ g t - Φ h₀ t
      rw [hper g t, hper h₀ t]
    have hclose : ∀ t : ℝ, ‖Φ g t - Φ h₀ t‖ < ‖Φ h₀ t₀‖ := by
      intro t
      obtain ⟨y, hy, hval⟩ := hdper.exists_mem_Ico₀ Real.two_pi_pos t
      have heq : Φ g t - Φ h₀ t = Φ g y - Φ h₀ y := hval
      rw [heq]
      exact huv (show (g, y) ∈ u ×ˢ v from ⟨hg, hKv (Ico_subset_Icc_self hy)⟩)
    have hloopg : Φ g 0 = Φ g (2 * Real.pi) := by
      have := hper g 0
      rw [zero_add] at this
      exact this.symm
    have hlooph : Φ h₀ 0 = Φ h₀ (2 * Real.pi) := by
      have := hper h₀ 0
      rw [zero_add] at this
      exact this.symm
    exact windingNumber_eq_of_close (hΦc h₀) (hΦc g) hlooph hloopg hlow hclose
  have hlc : IsLocallyConstant fun g : G => windingNumber (Φ g) 0 (2 * Real.pi) := by
    intro s
    rw [isOpen_iff_mem_nhds]
    intro g hg
    filter_upwards [hev g] with g' hg'
    simp only [Set.mem_preimage] at hg ⊢
    rw [hg']
    exact hg
  exact hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ g₀) (mem_univ g₁)

/-- The deck charge of a jointly continuous nonvanishing periodic family over a preconnected
parameter space is a single class. -/
theorem loopCharge_const_of_preconnected {G : Type*} [TopologicalSpace G] [PreconnectedSpace G]
    (k : ℕ) (Φ : G → ℝ → ℂ) (hc : Continuous fun p : G × ℝ => Φ p.1 p.2)
    (hnv : ∀ g t, Φ g t ≠ 0) (hper : ∀ g, Function.Periodic (Φ g) (2 * Real.pi))
    (g₀ g₁ : G) :
    loopCharge k (Φ g₀) 0 (2 * Real.pi) = loopCharge k (Φ g₁) 0 (2 * Real.pi) := by
  unfold loopCharge
  rw [windingNumber_const_of_preconnected Φ hc hnv hper g₀ g₁]

/-- **The connected-symmetry conjecture is false as a mechanism.**  At any positive level, no
family of nonvanishing periodic loops over a preconnected parameter space — in particular no orbit
map of a connected symmetry group carrying a window along — can realize every deck class: the
charge map cannot be surjective onto `ZMod (2^k)`.  Conservation (constancy on connected
parameters) and class-surjectivity are jointly unsatisfiable; what survives of such a conjecture
is only the component structure of the deformation space itself. -/
theorem not_surjective_loopCharge_of_preconnected {G : Type*} [TopologicalSpace G]
    [PreconnectedSpace G] {k : ℕ} (hk : k ≠ 0)
    (Φ : G → ℝ → ℂ) (hc : Continuous fun p : G × ℝ => Φ p.1 p.2)
    (hnv : ∀ g t, Φ g t ≠ 0) (hper : ∀ g, Function.Periodic (Φ g) (2 * Real.pi)) :
    ¬ Function.Surjective (fun g => loopCharge k (Φ g) 0 (2 * Real.pi)) := by
  intro hsurj
  haveI : Fact (1 < 2 ^ k) := ⟨Nat.one_lt_two_pow_iff.mpr hk⟩
  obtain ⟨g₀, hg₀⟩ := hsurj 0
  obtain ⟨g₁, hg₁⟩ := hsurj 1
  have h0' : loopCharge k (Φ g₀) 0 (2 * Real.pi) = 0 := hg₀
  have h1' : loopCharge k (Φ g₁) 0 (2 * Real.pi) = 1 := hg₁
  have hconst := loopCharge_const_of_preconnected k Φ hc hnv hper g₀ g₁
  rw [h0', h1'] at hconst
  exact zero_ne_one hconst

/-! ### §3 Conservation on the pair space: member and window move together -/

/-- The boundary loop of a moving window is `2π`-periodic in the angle. -/
theorem circleLoop_periodic (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    Function.Periodic (fun θ : ℝ => f (c + ↑r * exp (I * ↑θ))) (2 * Real.pi) := by
  intro θ
  have hexp : exp (I * ↑(θ + 2 * Real.pi)) = exp (I * ↑θ) := by
    push_cast
    rw [mul_add, Complex.exp_add,
      show I * (2 * (Real.pi : ℂ)) = 2 * (Real.pi : ℂ) * I by ring,
      Complex.exp_two_pi_mul_I, mul_one]
  show f (c + ↑r * exp (I * ↑(θ + 2 * Real.pi))) = f (c + ↑r * exp (I * ↑θ))
  rw [hexp]

/-- **Deck charge over a preconnected family of window pairs.**  If both the member and the window
vary over a preconnected parameter space, jointly continuously and with nonvanishing boundary, the
box charge is a single class. -/
theorem boxCharge_const_of_preconnected {G : Type*} [TopologicalSpace G] [PreconnectedSpace G]
    (k : ℕ) (F : G → ℂ → ℂ) (c : G → ℂ) (r : G → ℝ)
    (hc : Continuous fun p : G × ℝ => F p.1 (c p.1 + ↑(r p.1) * exp (I * ↑p.2)))
    (hnv : ∀ (g : G) (θ : ℝ), F g (c g + ↑(r g) * exp (I * ↑θ)) ≠ 0)
    (g₀ g₁ : G) :
    boxCharge k (F g₀) (c g₀) (r g₀) = boxCharge k (F g₁) (c g₁) (r g₁) := by
  rw [boxCharge, boxCharge]
  exact loopCharge_const_of_preconnected k
    (fun g (θ : ℝ) => F g (c g + ↑(r g) * exp (I * ↑θ))) hc hnv
    (fun g => circleLoop_periodic (F g) (c g) (r g)) g₀ g₁

/-- **Moving-pair conservation.**  Along a deformation that moves the member AND the window while
the boundary circle stays nonvanishing, the box charge is conserved — the fixed-circle
conservation law extended to the full pair `(member, window)`. -/
theorem boxCharge_conserved_moving (k : ℕ) {F : ℝ → ℂ → ℂ} {c : ℝ → ℂ} {r : ℝ → ℝ}
    (hc : Continuous fun p : ℝ × ℝ => F p.1 (c p.1 + ↑(r p.1) * exp (I * ↑p.2)))
    (hnv : ∀ σ θ : ℝ, F σ (c σ + ↑(r σ) * exp (I * ↑θ)) ≠ 0) :
    boxCharge k (F 0) (c 0) (r 0) = boxCharge k (F 1) (c 1) (r 1) :=
  boxCharge_const_of_preconnected k F c r hc hnv 0 1

/-! ### §4 Vacuum pairs carry zero charge -/

set_option maxHeartbeats 1000000 in
/-- **Vacuum has no charge.**  A member continuous and nonvanishing on the closed window has box
charge zero: the boundary loop contracts radially to the centre value through nonvanishing
loops. -/
theorem boxCharge_eq_zero_of_vacuum (k : ℕ) {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hfc : ContinuousOn f (closedBall c r))
    (hnv : ∀ z ∈ closedBall c r, f z ≠ 0) :
    boxCharge k f c r = 0 := by
  set clamp : ℝ → ℝ := fun σ => min 1 (max 0 σ) with hclampdef
  have hclamp_cont : Continuous clamp := continuous_const.min (continuous_const.max continuous_id)
  have hcl0 : ∀ σ, 0 ≤ clamp σ := fun σ => le_min zero_le_one (le_max_left 0 σ)
  have hcl1 : ∀ σ, clamp σ ≤ 1 := fun σ => min_le_left _ _
  have hmem : ∀ σ θ : ℝ, c + ↑(clamp σ * r) * exp (I * ↑θ) ∈ closedBall c r := by
    intro σ θ
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, show I * (θ : ℂ) = (θ : ℂ) * I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_nonneg (mul_nonneg (hcl0 σ) hr)]
    calc clamp σ * r ≤ 1 * r := mul_le_mul_of_nonneg_right (hcl1 σ) hr
    _ = r := one_mul r
  have hφc : Continuous fun p : ℝ × ℝ => c + ↑(clamp p.1 * r) * exp (I * ↑p.2) :=
    continuous_const.add
      ((Complex.continuous_ofReal.comp ((hclamp_cont.comp continuous_fst).mul
        continuous_const)).mul
        (Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp continuous_snd))))
  have hH := windingNumber_of_homotopic
    (γ₀ := fun _ => f c) (γ₁ := fun θ => f (c + ↑r * exp (I * ↑θ)))
    (a := 0) (b := 2 * Real.pi)
    (fun σ θ => f (c + ↑(clamp σ * r) * exp (I * ↑θ)))
    (hfc.comp_continuous hφc fun p => hmem p.1 p.2)
    (fun σ θ => hnv _ (hmem σ θ))
    (fun σ => by
      have := circleLoop_periodic f c (clamp σ * r) 0
      rw [zero_add] at this
      exact this.symm)
    (fun t => by
      have hc0 : clamp 0 = 0 := by norm_num [hclampdef]
      show f (c + ↑(clamp 0 * r) * exp (I * ↑t)) = f c
      rw [hc0, zero_mul]
      simp)
    (fun t => by
      have hc1 : clamp 1 = 1 := by norm_num [hclampdef]
      show f (c + ↑(clamp 1 * r) * exp (I * ↑t)) = f (c + ↑r * exp (I * ↑t))
      rw [hc1, one_mul])
  have hc0 : f c ≠ 0 := hnv c (mem_closedBall_self hr)
  rw [boxCharge, loopCharge, ← hH, windingNumber_const hc0]
  simp [wCharge]

/-! ### §5 The Riemann Hypothesis as absence of protected defects -/

/-- **RH ⟺ no right-half ξ-defect is topologically protected.**  For every level `k` and every
hypothetical right-half zero, some isolating window pair around it deforms — member and window
moving together, boundary never vanishing — to a vacuum pair.  Backward: the charge is conserved
along the deformation and vanishes on vacuum, while on the isolating window it reads the vanishing
order mod `2^k`; all levels force the order to be `0`, contradicting the zero.  Forward: under RH
the right half carries no zeros, so the clause is vacuous. -/
theorem rh_iff_no_protected_defect :
    RiemannHypothesis ↔
      ∀ k : ℕ, ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ (F : ℝ → ℂ → ℂ) (c : ℝ → ℂ) (r : ℝ → ℝ) (R : ℝ),
          F 0 = xi ∧ c 0 = ρ ∧ 0 < r 0 ∧ r 0 < R ∧
          (∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0) ∧
          Continuous (fun p : ℝ × ℝ => F p.1 (c p.1 + ↑(r p.1) * exp (I * ↑p.2))) ∧
          (∀ σ θ : ℝ, F σ (c σ + ↑(r σ) * exp (I * ↑θ)) ≠ 0) ∧
          0 ≤ r 1 ∧
          ContinuousOn (F 1) (closedBall (c 1) (r 1)) ∧
          (∀ z ∈ closedBall (c 1) (r 1), F 1 z ≠ 0) := by
  constructor
  · intro hRH k ρ hρ hzero
    exact absurd hzero (rh_iff_xi_ne_zero_right.mp hRH ρ hρ)
  · intro hdef
    rw [rh_iff_xi_ne_zero_right]
    intro ρ hρ hzero
    have hdvd : ∀ k : ℕ, 2 ^ k ∣ (analyticOrderAt xi ρ).toNat := by
      intro k
      obtain ⟨F, c, r, R, hF0, hc0, hr0, hrR, hiso, hcont, hnv, hr1, hF1c, hF1nv⟩ :=
        hdef k ρ hρ hzero
      obtain ⟨h, hhan, hh0, hfact⟩ := xi_peel_isolating_ball ρ hiso
      have hread : boxCharge k xi ρ (r 0) =
          wCharge (2 ^ k) (((analyticOrderAt xi ρ).toNat : ℤ)) :=
        boxCharge_single k hrR hr0 (by simpa using hr0) hhan.continuousOn hh0 hfact
      have hzero' : wCharge (2 ^ k) (((analyticOrderAt xi ρ).toNat : ℤ)) = 0 := by
        rw [← hread, ← hF0, ← hc0, boxCharge_conserved_moving k hcont hnv,
          boxCharge_eq_zero_of_vacuum k hr1 hF1c hF1nv]
      haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
      have hdd := (wCharge_eq_zero_iff (((analyticOrderAt xi ρ).toNat : ℤ))).mp hzero'
      exact_mod_cast hdd
    have hm0 : (analyticOrderAt xi ρ).toNat = 0 := by
      by_contra hm0
      have h2 : 2 ^ (analyticOrderAt xi ρ).toNat ≤ (analyticOrderAt xi ρ).toNat :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (hdvd _)
      have h3 : (analyticOrderAt xi ρ).toNat < 2 ^ (analyticOrderAt xi ρ).toNat :=
        Nat.lt_pow_self (by norm_num)
      omega
    have hmcoe : (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) = analyticOrderAt xi ρ :=
      ENat.coe_toNat (xi_orderAt_ne_top ρ)
    have hne : analyticOrderAt xi ρ ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨xi_analyticOnNhd_univ ρ (Set.mem_univ ρ), hzero⟩
    rw [← hmcoe, hm0] at hne
    exact hne rfl

end RHTower
