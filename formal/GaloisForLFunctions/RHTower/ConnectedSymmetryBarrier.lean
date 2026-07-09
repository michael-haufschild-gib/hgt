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
/-- **Vacuum windows have zero winding.**  A member continuous and nonvanishing on the closed
window has boundary loop of winding number zero: the loop contracts radially to the centre value
through nonvanishing loops. -/
theorem windingNumber_circleLoop_eq_zero_of_vacuum {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hfc : ContinuousOn f (closedBall c r))
    (hnv : ∀ z ∈ closedBall c r, f z ≠ 0) :
    windingNumber (fun θ : ℝ => f (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi) = 0 := by
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
  rw [← hH, windingNumber_const hc0]

/-- **Vacuum has no charge.**  A member continuous and nonvanishing on the closed window has box
charge zero at every level. -/
theorem boxCharge_eq_zero_of_vacuum (k : ℕ) {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hfc : ContinuousOn f (closedBall c r))
    (hnv : ∀ z ∈ closedBall c r, f z ≠ 0) :
    boxCharge k f c r = 0 := by
  rw [boxCharge, loopCharge, windingNumber_circleLoop_eq_zero_of_vacuum hr hfc hnv]
  simp [wCharge]

/-! ### §5 The defect invariant is complete: π₀ of the loop space is the winding number -/

/-- **Equal winding numbers produce a homotopy.**  Two nonvanishing loops with the same winding
number are joined by a homotopy through nonvanishing loops: interpolate their canonical
logarithms linearly; the equal increment `2πi·w` at both ends makes every intermediate curve a
loop, and the exponential never vanishes. -/
theorem joined_of_windingNumber_eq {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ}
    (h₀ : IsLoop γ₀ a b) (h₁ : IsLoop γ₁ a b)
    (hw : windingNumber γ₀ a b = windingNumber γ₁ a b) :
    ∃ H : ℝ → ℝ → ℂ,
      Continuous (fun p : ℝ × ℝ => H p.1 p.2) ∧
      (∀ σ t, H σ t ≠ 0) ∧ (∀ σ, H σ a = H σ b) ∧
      (∀ t, H 0 t = γ₀ t) ∧ (∀ t, H 1 t = γ₁ t) := by
  obtain ⟨hL₀c, hL₀e⟩ := contLog_spec h₀.continuous h₀.nonzero
  obtain ⟨hL₁c, hL₁e⟩ := contLog_spec h₁.continuous h₁.nonzero
  have hinc₀ := contLog_increment h₀ hL₀c hL₀e
  have hinc₁ := contLog_increment h₁ hL₁c hL₁e
  refine ⟨fun σ t => exp ((1 - (σ : ℂ)) * contLog γ₀ t + (σ : ℂ) * contLog γ₁ t),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.continuous_exp.comp
      (((continuous_const.sub (Complex.continuous_ofReal.comp continuous_fst)).mul
        (hL₀c.comp continuous_snd)).add
        ((Complex.continuous_ofReal.comp continuous_fst).mul (hL₁c.comp continuous_snd)))
  · intro σ t
    exact Complex.exp_ne_zero _
  · intro σ
    show exp ((1 - (σ : ℂ)) * contLog γ₀ a + (σ : ℂ) * contLog γ₁ a) =
      exp ((1 - (σ : ℂ)) * contLog γ₀ b + (σ : ℂ) * contLog γ₁ b)
    have hb₀ : contLog γ₀ b =
        contLog γ₀ a + ↑(windingNumber γ₀ a b) * (2 * (Real.pi : ℂ) * I) := by
      linear_combination hinc₀
    have hb₁ : contLog γ₁ b =
        contLog γ₁ a + ↑(windingNumber γ₀ a b) * (2 * (Real.pi : ℂ) * I) := by
      rw [hw]
      linear_combination hinc₁
    rw [hb₀, hb₁,
      show (1 - (σ : ℂ)) * (contLog γ₀ a +
            ↑(windingNumber γ₀ a b) * (2 * (Real.pi : ℂ) * I)) +
          (σ : ℂ) * (contLog γ₁ a + ↑(windingNumber γ₀ a b) * (2 * (Real.pi : ℂ) * I)) =
          ((1 - (σ : ℂ)) * contLog γ₀ a + (σ : ℂ) * contLog γ₁ a) +
            ↑(windingNumber γ₀ a b) * (2 * (Real.pi : ℂ) * I) from by ring]
    conv_rhs => rw [Complex.exp_add]
    rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · intro t
    show exp ((1 - ((0 : ℝ) : ℂ)) * contLog γ₀ t + ((0 : ℝ) : ℂ) * contLog γ₁ t) = γ₀ t
    rw [Complex.ofReal_zero, sub_zero, one_mul, zero_mul, add_zero]
    exact hL₀e t
  · intro t
    show exp ((1 - ((1 : ℝ) : ℂ)) * contLog γ₀ t + ((1 : ℝ) : ℂ) * contLog γ₁ t) = γ₁ t
    rw [Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add]
    exact hL₁e t

/-- **The classification of defects: π₀ of the nonvanishing loop space is exactly the winding
number.**  Two nonvanishing loops are joined by a homotopy through nonvanishing loops IFF their
winding numbers agree — the deck charge is a complete deformation invariant, not merely a
conserved one.  A window defect is therefore protected exactly when its total winding is nonzero;
nothing finer than the charge obstructs deformation. -/
theorem windingNumber_eq_iff_joined {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ}
    (h₀ : IsLoop γ₀ a b) (h₁ : IsLoop γ₁ a b) :
    windingNumber γ₀ a b = windingNumber γ₁ a b ↔
      ∃ H : ℝ → ℝ → ℂ,
        Continuous (fun p : ℝ × ℝ => H p.1 p.2) ∧
        (∀ σ t, H σ t ≠ 0) ∧ (∀ σ, H σ a = H σ b) ∧
        (∀ t, H 0 t = γ₀ t) ∧ (∀ t, H 1 t = γ₁ t) := by
  constructor
  · exact joined_of_windingNumber_eq h₀ h₁
  · rintro ⟨H, hc, hnv, hloop, hH0, hH1⟩
    exact windingNumber_of_homotopic H hc hnv hloop hH0 hH1

/-! ### §6 The Riemann Hypothesis as absence of protected defects -/

/-- **RH ⟺ no right-half ξ-defect is topologically protected.**  Around every hypothetical
right-half zero, some isolating window pair deforms — member and window moving together, boundary
never vanishing — to a vacuum pair.  The certificate is level-free: ONE deformation kills every
dyadic level at once.  Backward: the charge is conserved along the deformation and vanishes on
vacuum, while on the isolating window it reads the vanishing order mod `2^k`; all levels force the
order to be `0`, contradicting the zero.  Forward: under RH the right half carries no zeros, so
the clause is vacuous. -/
theorem rh_iff_no_protected_defect :
    RiemannHypothesis ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∃ (F : ℝ → ℂ → ℂ) (c : ℝ → ℂ) (r : ℝ → ℝ) (R : ℝ),
          F 0 = xi ∧ c 0 = ρ ∧ 0 < r 0 ∧ r 0 < R ∧
          (∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0) ∧
          Continuous (fun p : ℝ × ℝ => F p.1 (c p.1 + ↑(r p.1) * exp (I * ↑p.2))) ∧
          (∀ σ θ : ℝ, F σ (c σ + ↑(r σ) * exp (I * ↑θ)) ≠ 0) ∧
          0 ≤ r 1 ∧
          ContinuousOn (F 1) (closedBall (c 1) (r 1)) ∧
          (∀ z ∈ closedBall (c 1) (r 1), F 1 z ≠ 0) := by
  constructor
  · intro hRH ρ hρ hzero
    exact absurd hzero (rh_iff_xi_ne_zero_right.mp hRH ρ hρ)
  · intro hdef
    rw [rh_iff_xi_ne_zero_right]
    intro ρ hρ hzero
    obtain ⟨F, c, r, R, hF0, hc0, hr0, hrR, hiso, hcont, hnv, hr1, hF1c, hF1nv⟩ :=
      hdef ρ hρ hzero
    obtain ⟨h, hhan, hh0, hfact⟩ := xi_peel_isolating_ball ρ hiso
    have hdvd : ∀ k : ℕ, 2 ^ k ∣ (analyticOrderAt xi ρ).toNat := by
      intro k
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

/-! ### §7 The seam-blind re-cut -/

/-- **RH ⟺ seam-blind windows are chargeless.**  For the FE-symmetric ξ every line-symmetric
window has its charge determined by line data, so the whole content of the Riemann Hypothesis
lives in the windows the seam cannot see: closed windows inside the open right half-plane, never
touching the critical line.  RH holds iff every such window carries zero deck charge at every
level — charge exists only where the seam can read it.  Backward: an off-line zero admits an
isolating seam-blind window whose charge reads its order mod `2^k`; all levels force order zero.
Forward: under RH seam-blind windows are vacuum. -/
theorem rh_iff_seam_blind_windows_chargeless :
    RiemannHypothesis ↔
      ∀ (k : ℕ) (c : ℂ) (r : ℝ), 0 ≤ r →
        (∀ z ∈ closedBall c r, 1 / 2 < z.re) → boxCharge k xi c r = 0 := by
  rw [rh_iff_xi_ne_zero_right]
  constructor
  · intro hRH k c r hr hhalf
    exact boxCharge_eq_zero_of_vacuum k hr xi_differentiable.continuous.continuousOn
      fun z hz => hRH z (mem_rightHalf.mpr (hhalf z hz))
  · intro hch ρ hρ hzero
    have hρhalf : 1 / 2 < ρ.re := mem_rightHalf.mp hρ
    obtain ⟨R, hR0, hiso⟩ := xi_exists_isolating_radius ρ
    set r' : ℝ := min (R / 2) ((ρ.re - 1 / 2) / 2) with hr'def
    have hr'0 : 0 < r' := lt_min (by linarith) (by linarith)
    have hr'R : r' < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hhalf : ∀ z ∈ closedBall ρ r', 1 / 2 < z.re := by
      intro z hz
      have hd : ‖z - ρ‖ ≤ r' := by rwa [mem_closedBall, dist_eq_norm] at hz
      have hre : |z.re - ρ.re| ≤ r' := le_trans (Complex.abs_re_le_norm (z - ρ)) hd
      have hr'le : r' ≤ (ρ.re - 1 / 2) / 2 := min_le_right _ _
      have := abs_le.mp hre
      linarith [this.1]
    obtain ⟨h, hhan, hh0, hfact⟩ := xi_peel_isolating_ball ρ hiso
    have hdvd : ∀ k : ℕ, 2 ^ k ∣ (analyticOrderAt xi ρ).toNat := by
      intro k
      have hread : boxCharge k xi ρ r' =
          wCharge (2 ^ k) (((analyticOrderAt xi ρ).toNat : ℤ)) :=
        boxCharge_single k hr'R hr'0 (by simpa using hr'0) hhan.continuousOn hh0 hfact
      have hzero' : wCharge (2 ^ k) (((analyticOrderAt xi ρ).toNat : ℤ)) = 0 := by
        rw [← hread]
        exact hch k ρ r' hr'0.le hhalf
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
