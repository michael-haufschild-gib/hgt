import GaloisForLFunctions.HTGeometry.HodgeEdgeCochain.GlobalExistence
import Mathlib.Dynamics.OmegaLimit

/-!
# The semiflow and its compact global attractor

This file formalises Theorem 3 of Boudourides, *Hodge Coercivity and Global Dynamics in Two-Field
Edge-Cochain Systems with MHD-Type Cancellation* (arXiv:2608.19360): on a coercive phase space the
two-field system generates a continuous semiflow with a positively invariant absorbing ball and a
compact global attractor `A = ω(B_R)`.

## Main results

* `AdmissibleSystem` — the data of §3: a nonnegative dissipative operator, an interaction in the
  cancellation class, positive viscosities, and time-independent forcings.
* `AdmissibleSystem.orbit`, `orbit_zero`, `orbit_add` — the semiflow.
* `AdmissibleSystem.continuous_flow` — continuity of the solution operator in the initial state.
* `energyBall_mapsTo` — positive invariance of `B_R` (**Theorem 3**).
* `attractor_nonempty`, `isCompact_attractor`, `isInvariant_attractor`,
  `attractor_attracts` — the compact global attractor.
-/

open Set Filter
open scoped InnerProductSpace NNReal Topology

namespace GaloisForLFunctions.HTGeometry.HodgeEdgeCochain

/-- The data of the two-field MHD-type system (5)–(6). -/
structure AdmissibleSystem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] where
  /-- The dissipative operator, the degree-one Hodge Laplacian in the paper. -/
  A : E →L[ℝ] E
  /-- The interaction. -/
  B : E →L[ℝ] E →L[ℝ] E
  /-- The velocity viscosity. -/
  nu : ℝ
  /-- The magnetic viscosity. -/
  eta : ℝ
  /-- The velocity forcing. -/
  f : E
  /-- The magnetic forcing. -/
  g : E
  /-- The interaction satisfies the trilinear antisymmetry (4). -/
  cancelling : IsCancelling B
  /-- The dissipative operator is nonnegative. -/
  nonneg : ∀ v : E, 0 ≤ ⟪A v, v⟫_ℝ
  /-- `ν > 0`. -/
  nu_pos : 0 < nu
  /-- `η > 0`. -/
  eta_pos : 0 < eta

namespace AdmissibleSystem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (S : AdmissibleSystem E)

/-- The global solution as a curve in the product phase space. -/
theorem exists_pair_isSolutionOn_Ici (x : E × E) :
    ∃ α : ℝ → E × E, α 0 = x ∧
      IsSolutionOn S.A S.B S.nu S.eta S.f S.g (fun t => (α t).1) (fun t => (α t).2) (Ici 0) := by
  obtain ⟨u, h, hu0, hh0, hsol⟩ :=
    exists_isSolutionOn_Ici S.cancelling S.nonneg S.nu_pos.le S.eta_pos.le x.1 x.2
  exact ⟨fun t => (u t, h t), by simp [hu0, hh0], hsol⟩

/-- The chosen global orbit through `x`. -/
noncomputable def orbit (x : E × E) : ℝ → E × E := (S.exists_pair_isSolutionOn_Ici x).choose

@[simp] theorem orbit_zero (x : E × E) : S.orbit x 0 = x :=
  (S.exists_pair_isSolutionOn_Ici x).choose_spec.1

theorem orbit_isSolution (x : E × E) :
    IsSolutionOn S.A S.B S.nu S.eta S.f S.g (fun t => (S.orbit x t).1)
      (fun t => (S.orbit x t).2) (Ici 0) :=
  (S.exists_pair_isSolutionOn_Ici x).choose_spec.2

/-- Two global solutions with the same initial datum coincide on `[0,∞)`. -/
theorem eq_of_isSolutionOn_Ici {u h ubar hbar : ℝ → E}
    (hsol : IsSolutionOn S.A S.B S.nu S.eta S.f S.g u h (Ici 0))
    (hsol2 : IsSolutionOn S.A S.B S.nu S.eta S.f S.g ubar hbar (Ici 0))
    (hu0 : u 0 = ubar 0) (hh0 : h 0 = hbar 0) :
    ∀ t ∈ Ici (0 : ℝ), u t = ubar t ∧ h t = hbar t := by
  intro t ht
  have hT : (0 : ℝ) ≤ t := ht
  have hres : IsSolutionOn S.A S.B S.nu S.eta S.f S.g u h (Icc 0 t) :=
    fun s hs => hsol s hs.1
  have hres2 : IsSolutionOn S.A S.B S.nu S.eta S.f S.g ubar hbar (Icc 0 t) :=
    fun s hs => hsol2 s hs.1
  have := isSolutionOn_unique S.cancelling S.nonneg S.nu_pos.le S.eta_pos.le hT hres hres2 hu0 hh0
  exact ⟨this.1 ⟨hT, le_rfl⟩, this.2 ⟨hT, le_rfl⟩⟩

/-- **The semiflow property.** -/
theorem orbit_add (x : E × E) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    S.orbit x (s + t) = S.orbit (S.orbit x s) t := by
  have hsolx := S.orbit_isSolution x
  -- the shifted orbit is a solution starting at `orbit x s`
  have hshift : IsSolutionOn S.A S.B S.nu S.eta S.f S.g
      (fun r => (S.orbit x (s + r)).1) (fun r => (S.orbit x (s + r)).2) (Ici 0) := by
    intro r hr
    have hr' : (0 : ℝ) ≤ r := hr
    have hsr : s + r ∈ Ici (0 : ℝ) := by
      simp only [mem_Ici]; linarith
    have hid : HasDerivAt (fun r : ℝ => s + r) 1 r := by
      simpa using (hasDerivAt_id r).const_add s
    refine ⟨?_, ?_⟩
    · have := ((hsolx (s + r) hsr).1).scomp r hid
      simpa [Function.comp_def] using this
    · have := ((hsolx (s + r) hsr).2).scomp r hid
      simpa [Function.comp_def] using this
  have hsoly := S.orbit_isSolution (S.orbit x s)
  have h0 : (S.orbit x (s + 0)) = S.orbit (S.orbit x s) 0 := by simp
  have := S.eq_of_isSolutionOn_Ici hshift hsoly (congrArg Prod.fst h0) (congrArg Prod.snd h0)
  have h1 := (this t ht).1
  have h2 := (this t ht).2
  exact Prod.ext h1 h2

/-! ## Continuity of the solution operator -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem aprioriRadius_mono (f g : E) {E0 E1 T : ℝ} (h : E0 ≤ E1) :
    aprioriRadius f g E0 T ≤ aprioriRadius f g E1 T := by
  refine Real.sqrt_le_sqrt ?_
  have : Real.exp T > 0 := Real.exp_pos T
  nlinarith

/-- The solution operator is Lipschitz on every energy ball. -/
theorem exists_lipschitzOnWith_flow {t : ℝ} (ht : 0 ≤ t) (rho : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun x : E × E => S.orbit x t)
      {x : E × E | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 ≤ rho} := by
  set R : ℝ := aprioriRadius S.f S.g rho t with hRdef
  set c : ℝ := 8 * ‖S.B‖ * R * t with hcdef
  have hKnn : (0 : ℝ) ≤ Real.sqrt (2 * Real.exp c) := Real.sqrt_nonneg _
  refine ⟨⟨Real.sqrt (2 * Real.exp c), hKnn⟩, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  -- the two orbits stay in the ball of radius `R`
  have hsolx : IsSolutionOn S.A S.B S.nu S.eta S.f S.g (fun s => (S.orbit x s).1)
      (fun s => (S.orbit x s).2) (Icc 0 t) := fun s hs => S.orbit_isSolution x s hs.1
  have hsoly : IsSolutionOn S.A S.B S.nu S.eta S.f S.g (fun s => (S.orbit y s).1)
      (fun s => (S.orbit y s).2) (Icc 0 t) := fun s hs => S.orbit_isSolution y s hs.1
  have hex : energy (fun s => (S.orbit x s).1) (fun s => (S.orbit x s).2) 0 ≤ rho := by
    simpa [energy] using hx
  have hey : energy (fun s => (S.orbit y s).1) (fun s => (S.orbit y s).2) 0 ≤ rho := by
    simpa [energy] using hy
  have hbx := norm_le_aprioriRadius S.cancelling S.nonneg S.nu_pos.le S.eta_pos.le ht hsolx
  have hby := norm_le_aprioriRadius S.cancelling S.nonneg S.nu_pos.le S.eta_pos.le ht hsoly
  have hbx1 : ∀ s ∈ Icc (0 : ℝ) t, ‖(S.orbit x s).1‖ ≤ R := fun s hs =>
    le_trans (hbx s hs).1 (aprioriRadius_mono S.f S.g hex)
  have hbx2 : ∀ s ∈ Icc (0 : ℝ) t, ‖(S.orbit x s).2‖ ≤ R := fun s hs =>
    le_trans (hbx s hs).2 (aprioriRadius_mono S.f S.g hex)
  have hby1 : ∀ s ∈ Icc (0 : ℝ) t, ‖(S.orbit y s).1‖ ≤ R := fun s hs =>
    le_trans (hby s hs).1 (aprioriRadius_mono S.f S.g hey)
  have hby2 : ∀ s ∈ Icc (0 : ℝ) t, ‖(S.orbit y s).2‖ ≤ R := fun s hs =>
    le_trans (hby s hs).2 (aprioriRadius_mono S.f S.g hey)
  have hkey := energy_diff_le S.nonneg S.nu_pos.le S.eta_pos.le hsolx hsoly hbx1 hbx2 hby1 hby2
    t ⟨ht, le_rfl⟩
  simp only [S.orbit_zero] at hkey
  -- convert the energy estimate into a distance estimate
  set a : ℝ := ‖(S.orbit x t).1 - (S.orbit y t).1‖ with hadef
  set b : ℝ := ‖(S.orbit x t).2 - (S.orbit y t).2‖ with hbdef
  have hann : 0 ≤ a := norm_nonneg _
  have hbnn : 0 ≤ b := norm_nonneg _
  have hd1 : ‖x.1 - y.1‖ ≤ dist x y := by
    rw [dist_eq_norm]
    exact norm_fst_le (x - y)
  have hd2 : ‖x.2 - y.2‖ ≤ dist x y := by
    rw [dist_eq_norm]
    exact norm_snd_le (x - y)
  have hdnn : (0 : ℝ) ≤ dist x y := dist_nonneg
  have hD : ‖x.1 - y.1‖ ^ 2 + ‖x.2 - y.2‖ ^ 2 ≤ 2 * dist x y ^ 2 := by
    nlinarith [norm_nonneg (x.1 - y.1), norm_nonneg (x.2 - y.2)]
  have hexpc : (0 : ℝ) < Real.exp c := Real.exp_pos c
  have hsq : a ^ 2 + b ^ 2 ≤ 2 * Real.exp c * dist x y ^ 2 := by
    have := hkey
    nlinarith [hD, hexpc]
  have hdist : dist (S.orbit x t) (S.orbit y t) = max a b := by
    rw [dist_eq_norm, hadef, hbdef, Prod.norm_def]
    rfl
  have hmaxsq : (max a b) ^ 2 ≤ 2 * Real.exp c * dist x y ^ 2 := by
    rcases max_cases a b with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> nlinarith
  have hKsq : (Real.sqrt (2 * Real.exp c)) ^ 2 = 2 * Real.exp c :=
    Real.sq_sqrt (by positivity)
  rw [hdist]
  have hmnn : 0 ≤ max a b := le_max_of_le_left hann
  show max a b ≤ Real.sqrt (2 * Real.exp c) * dist x y
  have hKd : 0 ≤ Real.sqrt (2 * Real.exp c) * dist x y := mul_nonneg hKnn hdnn
  have hsq2 : (max a b) ^ 2 ≤ (Real.sqrt (2 * Real.exp c) * dist x y) ^ 2 := by
    rw [mul_pow, hKsq]
    exact hmaxsq
  have := Real.sqrt_le_sqrt hsq2
  rwa [Real.sqrt_sq hmnn, Real.sqrt_sq hKd] at this

/-- **Continuity of the semiflow in the initial state.** -/
theorem continuous_flow {t : ℝ} (ht : 0 ≤ t) : Continuous fun x : E × E => S.orbit x t := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨K, hK⟩ := S.exists_lipschitzOnWith_flow ht (2 * (‖x₀‖ + 1) ^ 2)
  have hsub : Metric.ball x₀ 1 ⊆ {x : E × E | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 ≤ 2 * (‖x₀‖ + 1) ^ 2} := by
    intro x hx
    have hxn : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have h1 : ‖x - x₀‖ < 1 := by rwa [← dist_eq_norm]
      have := norm_le_norm_add_norm_sub' x x₀
      linarith
    have h1 : ‖x.1‖ ≤ ‖x‖ := norm_fst_le x
    have h2 : ‖x.2‖ ≤ ‖x‖ := norm_snd_le x
    have h3 : (0 : ℝ) ≤ ‖x₀‖ + 1 := by positivity
    show ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 ≤ 2 * (‖x₀‖ + 1) ^ 2
    nlinarith [norm_nonneg x, norm_nonneg x.1, norm_nonneg x.2]
  exact hK.continuousOn.continuousAt (Filter.mem_of_superset (Metric.ball_mem_nhds x₀ one_pos) hsub)

/-! ## The absorbing ball and the global attractor -/

/-- The energy ball `B_R = {(u,h) : ‖u‖² + ‖h‖² ≤ R²}` of Theorem 3. -/
def energyBall (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (R : ℝ) :
    Set (E × E) := {x : E × E | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 ≤ R ^ 2}

theorem isClosed_energyBall (R : ℝ) : IsClosed (energyBall E R) := by
  have : Continuous fun x : E × E => ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 := by fun_prop
  simpa [energyBall] using isClosed_le this continuous_const

theorem energyBall_subset_closedBall (R : ℝ) :
    energyBall E R ⊆ Metric.closedBall (0 : E × E) |R| := by
  intro x hx
  have hx' : ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 ≤ R ^ 2 := hx
  have h1 : ‖x.1‖ ≤ |R| := by
    have : ‖x.1‖ ^ 2 ≤ |R| ^ 2 := by rw [sq_abs]; nlinarith [norm_nonneg x.2]
    nlinarith [norm_nonneg x.1, abs_nonneg R]
  have h2 : ‖x.2‖ ≤ |R| := by
    have : ‖x.2‖ ^ 2 ≤ |R| ^ 2 := by rw [sq_abs]; nlinarith [norm_nonneg x.1]
    nlinarith [norm_nonneg x.2, abs_nonneg R]
  simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le h1 h2

theorem isCompact_energyBall (R : ℝ) : IsCompact (energyBall E R) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_energyBall R)
    ((Metric.isBounded_closedBall).subset (energyBall_subset_closedBall R))

theorem energyBall_nonempty (R : ℝ) : (energyBall E R).Nonempty :=
  ⟨0, by simp [energyBall]; positivity⟩

variable {lam : ℝ}

/-- **Theorem 3 (positive invariance).**  On a coercive phase space every energy ball of radius
`R > F/β` is positively invariant under the semiflow. -/
theorem energyBall_mapsTo (hcoe : ∀ v : E, lam * ‖v‖ ^ 2 ≤ ⟪S.A v, v⟫_ℝ) (hlam : 0 < lam)
    {R : ℝ} (hR : Real.sqrt (‖S.f‖ ^ 2 + ‖S.g‖ ^ 2) / decayRate S.nu S.eta lam < R)
    {t : ℝ} (ht : 0 ≤ t) :
    MapsTo (fun x => S.orbit x t) (energyBall E R) (energyBall E R) := by
  intro x hx
  have hsolx : IsSolutionOn S.A S.B S.nu S.eta S.f S.g (fun s => (S.orbit x s).1)
      (fun s => (S.orbit x s).2) (Icc 0 t) := fun s hs => S.orbit_isSolution x s hs.1
  have h0 : energy (fun s => (S.orbit x s).1) (fun s => (S.orbit x s).2) 0 ≤ R ^ 2 := by
    simpa [energy, energyBall] using hx
  have := absorbing_ball_positively_invariant S.cancelling hcoe S.nu_pos S.eta_pos hlam
    hsolx hR h0 t ⟨ht, le_rfl⟩
  simpa [energyBall, energy] using this

/-- **Theorem 3 (absorption).**  Every energy-bounded set of initial data is carried into `B_R`
after a uniform time. -/
theorem exists_absorbing (hcoe : ∀ v : E, lam * ‖v‖ ^ 2 ≤ ⟪S.A v, v⟫_ℝ) (hlam : 0 < lam)
    {R rho : ℝ} (hR : Real.sqrt (‖S.f‖ ^ 2 + ‖S.g‖ ^ 2) / decayRate S.nu S.eta lam < R)
    (hrho : 0 ≤ rho) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ t, T₀ ≤ t →
      MapsTo (fun x => S.orbit x t) {x : E × E | ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 ≤ rho} (energyBall E R) := by
  obtain ⟨T₀, hT₀, habs⟩ := exists_absorbing_time (A := S.A) (B := S.B) (f := S.f) (g := S.g)
    (lam := lam) S.nu_pos S.eta_pos hlam hR hrho
  refine ⟨T₀, hT₀, fun t htt x hx => ?_⟩
  have ht0 : (0 : ℝ) ≤ t := le_trans hT₀ htt
  have hsolx : IsSolutionOn S.A S.B S.nu S.eta S.f S.g (fun s => (S.orbit x s).1)
      (fun s => (S.orbit x s).2) (Icc 0 t) := fun s hs => S.orbit_isSolution x s hs.1
  have h0 : energy (fun s => (S.orbit x s).1) (fun s => (S.orbit x s).2) 0 ≤ rho := by
    simpa [energy] using hx
  have := habs S.cancelling hsolx hcoe h0 t ⟨ht0, le_rfl⟩ htt
  simpa [energyBall, energy] using this

/-! ### The semiflow indexed by nonnegative times -/

/-- The semiflow `S(t)` on nonnegative times. -/
noncomputable def flow (t : ℝ≥0) (x : E × E) : E × E := S.orbit x (t : ℝ)

@[simp] theorem flow_zero (x : E × E) : S.flow 0 x = x := by
  simp [flow]

theorem flow_add (t₁ t₂ : ℝ≥0) (x : E × E) : S.flow (t₁ + t₂) x = S.flow t₁ (S.flow t₂ x) := by
  have h := S.orbit_add x (s := (t₂ : ℝ)) (t := (t₁ : ℝ)) t₂.coe_nonneg t₁.coe_nonneg
  simp only [flow, NNReal.coe_add]
  rw [add_comm ((t₁ : ℝ)) ((t₂ : ℝ))]
  exact h

theorem continuous_flow' (t : ℝ≥0) : Continuous (S.flow t) := S.continuous_flow t.coe_nonneg

/-- **Theorem 3.**  The global attractor `A = ω(B_R)`. -/
noncomputable def attractor (R : ℝ) : Set (E × E) :=
  omegaLimit Filter.atTop S.flow (energyBall E R)

theorem attractor_subset (hcoe : ∀ v : E, lam * ‖v‖ ^ 2 ≤ ⟪S.A v, v⟫_ℝ) (hlam : 0 < lam)
    {R : ℝ} (hR : Real.sqrt (‖S.f‖ ^ 2 + ‖S.g‖ ^ 2) / decayRate S.nu S.eta lam < R) :
    S.attractor R ⊆ energyBall E R := by
  have hinv : image2 S.flow (univ : Set ℝ≥0) (energyBall E R) ⊆ energyBall E R := by
    rintro _ ⟨t, -, x, hx, rfl⟩
    exact S.energyBall_mapsTo hcoe hlam hR t.coe_nonneg hx
  refine le_trans (omegaLimit_subset_closure_image2 Filter.atTop S.flow (energyBall E R)
    Filter.univ_mem) ?_
  exact closure_minimal hinv (isClosed_energyBall R)

theorem isClosed_attractor (R : ℝ) : IsClosed (S.attractor R) := isClosed_omegaLimit _ _ _

/-- **Theorem 3.**  The attractor is compact. -/
theorem isCompact_attractor (hcoe : ∀ v : E, lam * ‖v‖ ^ 2 ≤ ⟪S.A v, v⟫_ℝ) (hlam : 0 < lam)
    {R : ℝ} (hR : Real.sqrt (‖S.f‖ ^ 2 + ‖S.g‖ ^ 2) / decayRate S.nu S.eta lam < R) :
    IsCompact (S.attractor R) :=
  (isCompact_energyBall R).of_isClosed_subset (S.isClosed_attractor R)
    (S.attractor_subset hcoe hlam hR)

/-- **Theorem 3.**  The attractor is nonempty. -/
theorem attractor_nonempty (hcoe : ∀ v : E, lam * ‖v‖ ^ 2 ≤ ⟪S.A v, v⟫_ℝ) (hlam : 0 < lam)
    {R : ℝ} (hR : Real.sqrt (‖S.f‖ ^ 2 + ‖S.g‖ ^ 2) / decayRate S.nu S.eta lam < R) :
    (S.attractor R).Nonempty := by
  have hinv : image2 S.flow (univ : Set ℝ≥0) (energyBall E R) ⊆ energyBall E R := by
    rintro _ ⟨t, -, x, hx, rfl⟩
    exact S.energyBall_mapsTo hcoe hlam hR t.coe_nonneg hx
  refine nonempty_omegaLimit_of_isCompact_absorbing Filter.atTop S.flow (energyBall E R)
    (isCompact_energyBall R) ⟨univ, Filter.univ_mem, ?_⟩ (energyBall_nonempty R)
  exact closure_minimal hinv (isClosed_energyBall R)

/-- **Theorem 3.**  The attractor is invariant under the semiflow. -/
theorem isInvariant_attractor (R : ℝ) : IsInvariant S.flow (S.attractor R) := by
  intro t
  have hshift : Filter.Tendsto (fun t' : ℝ≥0 => t + t') Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun _ => le_add_self) Filter.tendsto_id
  refine MapsTo.mono_right ?_ (omegaLimit_subset_of_tendsto S.flow (energyBall E R) hshift)
  exact mapsTo_omegaLimit _ (mapsTo_id _) (fun t' x => (S.flow_add t t' x).symm)
    (S.continuous_flow' t)

/-- **Theorem 3.**  The attractor attracts the absorbing ball: every open neighbourhood of `A`
eventually contains the image of `B_R`. -/
theorem attractor_attracts (hcoe : ∀ v : E, lam * ‖v‖ ^ 2 ≤ ⟪S.A v, v⟫_ℝ) (hlam : 0 < lam)
    {R : ℝ} (hR : Real.sqrt (‖S.f‖ ^ 2 + ‖S.g‖ ^ 2) / decayRate S.nu S.eta lam < R)
    {n : Set (E × E)} (hn : IsOpen n) (hsub : S.attractor R ⊆ n) :
    ∀ᶠ t in Filter.atTop, MapsTo (S.flow t) (energyBall E R) n := by
  refine eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset Filter.atTop
    S.flow (energyBall E R) (isCompact_energyBall R) ?_ hn hsub
  filter_upwards with t
  exact fun x hx => S.energyBall_mapsTo hcoe hlam hR t.coe_nonneg hx

end AdmissibleSystem

end GaloisForLFunctions.HTGeometry.HodgeEdgeCochain
