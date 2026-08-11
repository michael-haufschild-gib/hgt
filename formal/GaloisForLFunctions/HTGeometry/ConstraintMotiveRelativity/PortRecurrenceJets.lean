import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PortAdmissionCapacity

/-!
# The port orbit: recurrence and the jet admission hierarchy

A square-summable coefficient family `c` and a phase family `θ` produce the orbit

`Φ t = (p ↦ c p · e^{-i t θ p})`

in the source chart.  Every finite aperture truncation of the orbit converges to it uniformly in
time, which makes the orbit norm-continuous, totally bounded, and — through the isometry of the
flow — recurrent: the orbit returns to within `ε` of its start at arbitrarily late times.

The same uniform-truncation argument differentiates the orbit term by term.  The `n`-th derivative
carries the coefficient `(-i θ p)^n c p`, so it is an admissible chart vector exactly when the
`n`-th jet capacity `C_n = ∑ θ p ^ (2n) ‖c p‖²` is finite, and the orbit is `C^n` exactly when
every jet capacity up to order `n` is finite.
-/

open scoped InnerProductSpace

namespace HTGeometry.ConstraintMotiveRelativity

section PortOrbit

variable {P : Type*} [DecidableEq P]

/-- The phase factor of the port orbit. -/
noncomputable def portPhase (θ : P → ℝ) (t : ℝ) (p : P) : ℂ :=
  Complex.exp (-(Complex.I * ((t * θ p : ℝ) : ℂ)))

omit [DecidableEq P] in
@[simp] theorem norm_portPhase (θ : P → ℝ) (t : ℝ) (p : P) : ‖portPhase θ t p‖ = 1 := by
  rw [portPhase, Complex.norm_exp]
  simp

omit [DecidableEq P] in
@[simp] theorem portPhase_zero (θ : P → ℝ) (p : P) : portPhase θ 0 p = 1 := by
  simp [portPhase]

omit [DecidableEq P] in
theorem portPhase_add (θ : P → ℝ) (t s : ℝ) (p : P) :
    portPhase θ (t + s) p = portPhase θ t p * portPhase θ s p := by
  rw [portPhase, portPhase, portPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The twisted coefficient family of the orbit. -/
noncomputable def portCoef (θ : P → ℝ) (c : P → ℂ) (t : ℝ) (p : P) : ℂ :=
  c p * portPhase θ t p

omit [DecidableEq P] in
@[simp] theorem norm_portCoef (θ : P → ℝ) (c : P → ℂ) (t : ℝ) (p : P) :
    ‖portCoef θ c t p‖ = ‖c p‖ := by
  rw [portCoef, norm_mul, norm_portPhase, mul_one]

omit [DecidableEq P] in
@[simp] theorem portCoef_zero (θ : P → ℝ) (c : P → ℂ) : portCoef θ c 0 = c := by
  funext p; simp [portCoef]

/-- The port orbit inside the source chart. -/
noncomputable def portOrbit (θ : P → ℝ) (c : P → ℂ) (h : Summable fun p => ‖c p‖ ^ 2) (t : ℝ) :
    SourceL2 P :=
  ⟨portCoef θ c t, memℓp_two_iff.2 (by simpa using h)⟩

omit [DecidableEq P] in
@[simp] theorem portOrbit_apply (θ : P → ℝ) (c : P → ℂ) (h : Summable fun p => ‖c p‖ ^ 2)
    (t : ℝ) (p : P) : (portOrbit θ c h t : P → ℂ) p = portCoef θ c t p := rfl

variable {θ : P → ℝ} {c : P → ℂ} {h : Summable fun p => ‖c p‖ ^ 2}

omit [DecidableEq P] in
theorem norm_portOrbit_sub_sq (t s : ℝ) :
    ‖portOrbit θ c h t - portOrbit θ c h s‖ ^ 2
      = ∑' p, ‖c p‖ ^ 2 * ‖portPhase θ t p - portPhase θ s p‖ ^ 2 := by
  rw [norm_sq_eq_tsum]
  refine tsum_congr fun p => ?_
  rw [lp.coeFn_sub]
  simp only [Pi.sub_apply, portOrbit_apply, portCoef]
  rw [← mul_sub, norm_mul, mul_pow]

omit [DecidableEq P] in
/-- The orbit is an isometric flow: the displacement over a time `t` does not depend on where the
flow starts. -/
theorem norm_portOrbit_shift (t s : ℝ) :
    ‖portOrbit θ c h (t + s) - portOrbit θ c h s‖
      = ‖portOrbit θ c h t - portOrbit θ c h 0‖ := by
  have hsq : ‖portOrbit θ c h (t + s) - portOrbit θ c h s‖ ^ 2
      = ‖portOrbit θ c h t - portOrbit θ c h 0‖ ^ 2 := by
    rw [norm_portOrbit_sub_sq, norm_portOrbit_sub_sq]
    refine tsum_congr fun p => ?_
    congr 1
    rw [portPhase_add, ← sub_one_mul, norm_mul, norm_portPhase, mul_one, portPhase_zero]
  have h1 := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1

/-- The chart embedding of a single coordinate, as a continuous linear map. -/
noncomputable def singleCLM (p : P) : ℂ →L[ℂ] SourceL2 P :=
  LinearMap.mkContinuous (lp.lsingle (𝕜 := ℂ) (E := fun _ : P => ℂ) 2 p) 1 fun a => by
    rw [one_mul]
    exact le_of_eq (lp.norm_single (E := fun _ : P => ℂ) (by norm_num) p a)

@[simp] theorem singleCLM_apply (p : P) (a : ℂ) : singleCLM p a = lp.single 2 p a := rfl

/-- The coordinate readout of the chart, as a continuous linear map. -/
noncomputable def coordCLM (p : P) : SourceL2 P →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => (f : P → ℂ) p
      map_add' := fun f g => by simp
      map_smul' := fun a f => by simp } 1 fun f => by
    rw [one_mul]
    exact lp.norm_apply_le_norm (by norm_num) f p

omit [DecidableEq P] in
@[simp] theorem coordCLM_apply (p : P) (f : SourceL2 P) : coordCLM p f = (f : P → ℂ) p := rfl

/-- The finite-aperture truncation of the orbit. -/
noncomputable def portTrunc (θ : P → ℝ) (c : P → ℂ) (F : Finset P) (t : ℝ) : SourceL2 P :=
  ∑ p ∈ F, singleCLM p (portCoef θ c t p)

theorem portTrunc_apply (F : Finset P) (t : ℝ) (q : P) :
    (portTrunc θ c F t : P → ℂ) q = if q ∈ F then portCoef θ c t q else 0 := by
  classical
  rw [portTrunc]
  simp only [singleCLM_apply, lp.coeFn_sum, Finset.sum_apply]
  exact Finset.sum_pi_single q (fun p => portCoef θ c t p) F

omit [DecidableEq P] in
theorem tsum_norm_compl_nonneg (F : Finset P) : 0 ≤ ∑' (p : {x : P // x ∉ F}), ‖c p‖ ^ 2 :=
  tsum_nonneg fun p => by positivity

theorem norm_portOrbit_sub_trunc_sq (F : Finset P) (t : ℝ) :
    ‖portOrbit θ c h t - portTrunc θ c F t‖ ^ 2 = ∑' (p : {x : P // x ∉ F}), ‖c p‖ ^ 2 := by
  classical
  rw [norm_sq_eq_tsum]
  have hcoord : ∀ q : P, ‖((portOrbit θ c h t - portTrunc θ c F t : SourceL2 P) : P → ℂ) q‖ ^ 2
      = Set.indicator {x : P | x ∉ F} (fun p => ‖c p‖ ^ 2) q := by
    intro q
    rw [lp.coeFn_sub]
    simp only [Pi.sub_apply, portOrbit_apply, portTrunc_apply]
    by_cases hq : q ∈ F
    · rw [if_pos hq, sub_self, Set.indicator_of_notMem (by simpa using hq)]
      simp
    · rw [if_neg hq, sub_zero, Set.indicator_of_mem (by simpa using hq), norm_portCoef]
  rw [tsum_congr hcoord, ← tsum_subtype {x : P | x ∉ F} fun p => ‖c p‖ ^ 2]
  rfl

/-- **The finite apertures converge to the orbit uniformly in time.** -/
theorem tendstoUniformly_portTrunc :
    TendstoUniformly (fun F : Finset P => portTrunc θ c F) (portOrbit θ c h) Filter.atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have htail := tendsto_tsum_compl_atTop_zero (fun p : P => ‖c p‖ ^ 2)
  have hev := (tendsto_order.1 htail).2 (ε ^ 2) (by positivity)
  filter_upwards [hev] with F hF t
  rw [dist_eq_norm]
  have hsq : ‖portOrbit θ c h t - portTrunc θ c F t‖ ^ 2 < ε ^ 2 := by
    rw [norm_portOrbit_sub_trunc_sq]
    exact hF
  nlinarith [norm_nonneg (portOrbit θ c h t - portTrunc θ c F t), hε.le]

omit [DecidableEq P] in
theorem continuous_portCoef (p : P) : Continuous fun t : ℝ => portCoef θ c t p := by
  unfold portCoef portPhase
  fun_prop

theorem continuous_portTrunc (F : Finset P) : Continuous (portTrunc θ c F) :=
  continuous_finsetSum _ fun p _ => (singleCLM p).continuous.comp (continuous_portCoef p)

/-- **Theorem 3, first clause.**  The port orbit is norm-continuous. -/
theorem continuous_portOrbit : Continuous (portOrbit θ c h) :=
  (tendstoUniformly_portTrunc (h := h)).continuous
    (Filter.Eventually.frequently (Filter.Eventually.of_forall continuous_portTrunc))

end PortOrbit

section Recurrence

variable {P : Type*} [DecidableEq P] {θ : P → ℝ} {c : P → ℂ} {h : Summable fun p => ‖c p‖ ^ 2}

/-- **Theorem 3, second clause.**  The port orbit is totally bounded: a finite aperture carries all
but `ε` of the mass, and the truncated orbit lives in a compact box. -/
theorem totallyBounded_range_portOrbit : TotallyBounded (Set.range (portOrbit θ c h)) := by
  classical
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨F, hF⟩ : ∃ F : Finset P, ∀ t, dist (portOrbit θ c h t) (portTrunc θ c F t) < ε / 3 :=
    ((Metric.tendstoUniformly_iff.1
      (tendstoUniformly_portTrunc (θ := θ) (c := c) (h := h))) (ε / 3) (by linarith)).exists
  set box : Set (P → ℂ) := Set.univ.pi fun p => Metric.closedBall (0 : ℂ) ‖c p‖ with hbox
  have hboxc : IsCompact box := isCompact_univ_pi fun p => isCompact_closedBall _ _
  set Ψ : (P → ℂ) → SourceL2 P := fun g => ∑ p ∈ F, singleCLM p (g p) with hΨ
  have hΨc : Continuous Ψ :=
    continuous_finsetSum _ fun p _ => (singleCLM p).continuous.comp (continuous_apply p)
  obtain ⟨net, hnetfin, hnet⟩ :=
    Metric.totallyBounded_iff.1 (hboxc.image hΨc).totallyBounded (ε / 3) (by linarith)
  refine ⟨net, hnetfin, ?_⟩
  rintro x ⟨r, rfl⟩
  have hmem : portTrunc θ c F r ∈ Ψ '' box := by
    refine ⟨portCoef θ c r, ?_, rfl⟩
    intro p _
    simp [Metric.mem_closedBall]
  obtain ⟨y, hy, hdy⟩ : ∃ y ∈ net, dist (portTrunc θ c F r) y < ε / 3 := by
    have hx := hnet hmem
    simpa [Set.mem_iUnion] using hx
  refine Set.mem_iUnion₂.2 ⟨y, hy, ?_⟩
  have htri := dist_triangle (portOrbit θ c h r) (portTrunc θ c F r) y
  rw [Metric.mem_ball]
  linarith [hF r]

/-- The closure of the orbit is compact. -/
theorem isCompact_closure_range_portOrbit :
    IsCompact (closure (Set.range (portOrbit θ c h))) :=
  (totallyBounded_range_portOrbit (θ := θ) (c := c) (h := h)).closure.isCompact_of_isClosed
    isClosed_closure

/-- **Theorem 3, third clause.**  The port orbit is recurrent: at arbitrarily late times it returns
to within `ε` of its starting point. -/
theorem portOrbit_recurrent {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ ‖portOrbit θ c h t - portOrbit θ c h 0‖ < ε := by
  classical
  set a : ℝ := max T 0 + 1 with ha
  have hmax : (0 : ℝ) ≤ max T 0 := le_max_right _ _
  have hapos : 0 < a := by rw [ha]; linarith
  have haT : T < a := by
    have : T ≤ max T 0 := le_max_left _ _
    rw [ha]; linarith
  obtain ⟨net, hnetfin, hnet⟩ :=
    Metric.totallyBounded_iff.1 (totallyBounded_range_portOrbit (θ := θ) (c := c) (h := h))
      (ε / 2) (by linarith)
  have hpick : ∀ n : ℕ, ∃ y ∈ net, dist (portOrbit θ c h ((n : ℝ) * a)) y < ε / 2 := by
    intro n
    have hx := hnet (Set.mem_range_self ((n : ℝ) * a))
    simpa [Set.mem_iUnion] using hx
  choose y hy hdy using hpick
  haveI : Finite ↥net := hnetfin.to_subtype
  obtain ⟨i, j, hij, hyij⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (⟨y n, hy n⟩ : ↥net))
  have hyeq : y i = y j := congrArg Subtype.val hyij
  have key : ∀ m n : ℕ, m < n → y m = y n →
      ∃ t : ℝ, T < t ∧ ‖portOrbit θ c h t - portOrbit θ c h 0‖ < ε := by
    intro m n hmn hyy
    have h1 : (1 : ℝ) ≤ (n : ℝ) - m := by
      have : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    refine ⟨((n : ℝ) - m) * a, ?_, ?_⟩
    · have h2 : a ≤ ((n : ℝ) - m) * a := le_mul_of_one_le_left hapos.le h1
      linarith
    · have hshift :=
        norm_portOrbit_shift (θ := θ) (c := c) (h := h) (((n : ℝ) - m) * a) ((m : ℝ) * a)
      have hsum : ((n : ℝ) - m) * a + (m : ℝ) * a = (n : ℝ) * a := by ring
      rw [hsum] at hshift
      rw [← hshift, ← dist_eq_norm]
      have d1 := hdy m
      have d2 := hdy n
      rw [hyy] at d1
      have htri := dist_triangle (portOrbit θ c h ((n : ℝ) * a)) (y n)
        (portOrbit θ c h ((m : ℝ) * a))
      rw [dist_comm (y n) (portOrbit θ c h ((m : ℝ) * a))] at htri
      linarith
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact key i j hlt hyeq
  · exact key j i hgt hyeq.symm

end Recurrence

section Jets

variable {P : Type*} [DecidableEq P]

/-- The `n`-jet coefficient family: differentiating the orbit `n` times multiplies the coefficient
by `(-i θ p)^n`. -/
noncomputable def jetCoef (θ : P → ℝ) (c : P → ℂ) (n : ℕ) (p : P) : ℂ :=
  (-(Complex.I * (θ p : ℂ))) ^ n * c p

omit [DecidableEq P] in
@[simp] theorem jetCoef_zero_order (θ : P → ℝ) (c : P → ℂ) : jetCoef θ c 0 = c := by
  funext p; simp [jetCoef]

omit [DecidableEq P] in
theorem jetCoef_one_jet (θ : P → ℝ) (c : P → ℂ) (n : ℕ) :
    jetCoef θ (jetCoef θ c 1) n = jetCoef θ c (n + 1) := by
  funext p
  simp only [jetCoef, pow_succ]
  ring

omit [DecidableEq P] in
theorem norm_jetCoef (θ : P → ℝ) (c : P → ℂ) (n : ℕ) (p : P) :
    ‖jetCoef θ c n p‖ = |θ p| ^ n * ‖c p‖ := by
  rw [jetCoef, norm_mul, norm_pow]
  congr 2
  simp

omit [DecidableEq P] in
/-- The `n`-jet capacity is `∑ θ p ^ (2n) ‖c p‖²`. -/
theorem norm_jetCoef_sq (θ : P → ℝ) (c : P → ℂ) (n : ℕ) (p : P) :
    ‖jetCoef θ c n p‖ ^ 2 = θ p ^ (2 * n) * ‖c p‖ ^ 2 := by
  rw [norm_jetCoef, mul_pow, ← pow_mul, mul_comm n 2, pow_mul, sq_abs, ← pow_mul]

variable {θ : P → ℝ} {c : P → ℂ}

omit [DecidableEq P] in
/-- The squared chart norm of the orbit is the total capacity, at every time. -/
theorem norm_portOrbit_sq (h : Summable fun p => ‖c p‖ ^ 2) (t : ℝ) :
    ‖portOrbit θ c h t‖ ^ 2 = ∑' p, ‖c p‖ ^ 2 := by
  rw [norm_sq_eq_tsum]
  exact tsum_congr fun p => by simp

omit [DecidableEq P] in
theorem hasDerivAt_portCoef (θ : P → ℝ) (c : P → ℂ) (t : ℝ) (p : P) :
    HasDerivAt (fun t : ℝ => portCoef θ c t p) (portCoef θ (jetCoef θ c 1) t p) t := by
  have h1 : HasDerivAt (fun t : ℝ => ((t * θ p : ℝ) : ℂ)) ((θ p : ℂ)) t := by
    simpa using ((hasDerivAt_id t).mul_const (θ p)).ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => -(Complex.I * ((t * θ p : ℝ) : ℂ)))
      (-(Complex.I * (θ p : ℂ))) t := (h1.const_mul Complex.I).neg
  have h4 := (h2.cexp).const_mul (c p)
  have h5 : c p * (Complex.exp (-(Complex.I * ((t * θ p : ℝ) : ℂ))) * -(Complex.I * (θ p : ℂ)))
      = portCoef θ (jetCoef θ c 1) t p := by
    simp only [portCoef, portPhase, jetCoef, pow_one]
    ring
  rw [← h5]
  exact h4

theorem hasDerivAt_portTrunc (F : Finset P) (t : ℝ) :
    HasDerivAt (portTrunc θ c F) (portTrunc θ (jetCoef θ c 1) F t) t := by
  have hterm : ∀ p ∈ F, HasDerivAt (fun t : ℝ => singleCLM p (portCoef θ c t p))
      (singleCLM p (portCoef θ (jetCoef θ c 1) t p)) t := by
    intro p _
    exact ((singleCLM p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_portCoef θ c t p)
  have hsum := HasDerivAt.sum hterm
  have hfun : (∑ p ∈ F, fun y : ℝ => singleCLM p (portCoef θ c y p))
      = fun y : ℝ => ∑ p ∈ F, singleCLM p (portCoef θ c y p) := by
    funext y
    simp [Finset.sum_apply]
  rw [hfun] at hsum
  exact hsum

/-- **Theorem 3, jet clause.**  The orbit differentiates term by term: the derivative is the orbit
of the once-twisted coefficient family. -/
theorem hasDerivAt_portOrbit (h : Summable fun p => ‖c p‖ ^ 2)
    (h1 : Summable fun p => ‖jetCoef θ c 1 p‖ ^ 2) (t : ℝ) :
    HasDerivAt (portOrbit θ c h) (portOrbit θ (jetCoef θ c 1) h1 t) t := by
  refine hasDerivAt_of_tendstoUniformlyOn (l := Filter.atTop) (s := Set.univ)
    (f := fun F : Finset P => portTrunc θ c F)
    (f' := fun F : Finset P => fun t => portTrunc θ (jetCoef θ c 1) F t)
    (g := portOrbit θ c h) (g' := portOrbit θ (jetCoef θ c 1) h1)
    isOpen_univ ?_ ?_ ?_ (Set.mem_univ t)
  · exact (tendstoUniformly_portTrunc (θ := θ) (c := jetCoef θ c 1) (h := h1)).tendstoUniformlyOn
  · exact Filter.Eventually.of_forall fun F t _ => hasDerivAt_portTrunc F t
  · exact fun t _ => (tendstoUniformly_portTrunc (θ := θ) (c := c) (h := h)).tendsto_at t

theorem deriv_portOrbit (h : Summable fun p => ‖c p‖ ^ 2)
    (h1 : Summable fun p => ‖jetCoef θ c 1 p‖ ^ 2) :
    deriv (portOrbit θ c h) = portOrbit θ (jetCoef θ c 1) h1 :=
  funext fun t => (hasDerivAt_portOrbit h h1 t).deriv

omit [DecidableEq P] in
/-- **Theorem 3, converse jet clause.**  A differentiable orbit forces a finite first jet capacity:
the coordinate readouts pin the derivative coefficients, and the derivative is a chart vector. -/
theorem summable_jetCoef_one_of_differentiableAt (h : Summable fun p => ‖c p‖ ^ 2)
    (hd : DifferentiableAt ℝ (portOrbit θ c h) 0) :
    Summable (fun p => ‖jetCoef θ c 1 p‖ ^ 2) := by
  set v : SourceL2 P := deriv (portOrbit θ c h) 0 with hvdef
  have hv : HasDerivAt (portOrbit θ c h) v 0 := hd.hasDerivAt
  have hcoord : ∀ p, (v : P → ℂ) p = jetCoef θ c 1 p := by
    intro p
    have hL : HasDerivAt (fun t : ℝ => portCoef θ c t p) ((v : P → ℂ) p) 0 :=
      ((coordCLM p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hv
    have hR : HasDerivAt (fun t : ℝ => portCoef θ c t p) (jetCoef θ c 1 p) 0 := by
      have h0 := hasDerivAt_portCoef θ c 0 p
      have hz : portCoef θ (jetCoef θ c 1) 0 p = jetCoef θ c 1 p := by simp [portCoef]
      rwa [hz] at h0
    exact hL.unique hR
  exact (memℓp_two_iff.1 v.2).congr fun p => by rw [hcoord p]

/-- **`(CA.9)`, the jet admission hierarchy.**  The orbit is `C^n` exactly when every jet capacity
up to order `n` is finite. -/
theorem contDiff_portOrbit_iff (θ : P → ℝ) :
    ∀ (n : ℕ) (c : P → ℂ) (h : Summable fun p => ‖c p‖ ^ 2),
      ContDiff ℝ n (portOrbit θ c h) ↔ ∀ k ≤ n, Summable (fun p => ‖jetCoef θ c k p‖ ^ 2) := by
  intro n
  induction n with
  | zero =>
      intro c h
      constructor
      · intro _ k hk
        interval_cases k
        simpa using h
      · intro _
        exact contDiff_zero.2 continuous_portOrbit
  | succ n ih =>
      intro c h
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; ring
      rw [hcast, contDiff_succ_iff_deriv]
      constructor
      · rintro ⟨hdiff, -, hcd⟩
        have h1 : Summable (fun p => ‖jetCoef θ c 1 p‖ ^ 2) :=
          summable_jetCoef_one_of_differentiableAt h (hdiff 0)
        rw [deriv_portOrbit h h1] at hcd
        have hprev := (ih (jetCoef θ c 1) h1).1 hcd
        intro k hk
        cases k with
        | zero => simpa using h
        | succ m =>
            have hm := hprev m (by omega)
            rwa [jetCoef_one_jet] at hm
      · intro hall
        have h1 : Summable (fun p => ‖jetCoef θ c 1 p‖ ^ 2) := hall 1 (by omega)
        refine ⟨fun t => (hasDerivAt_portOrbit h h1 t).differentiableAt, ?_, ?_⟩
        · intro hcon
          exact absurd hcon (by simp)
        · rw [deriv_portOrbit h h1]
          refine (ih (jetCoef θ c 1) h1).2 fun k hk => ?_
          rw [jetCoef_one_jet]
          exact hall (k + 1) (by omega)

omit [DecidableEq P] in
theorem portOrbit_congr {c c' : P → ℂ} (hcc : c = c') (h : Summable fun p => ‖c p‖ ^ 2)
    (h' : Summable fun p => ‖c' p‖ ^ 2) : portOrbit θ c h = portOrbit θ c' h' := by
  subst hcc; rfl

omit [DecidableEq P] in
theorem jetCoef_jet_one (θ : P → ℝ) (c : P → ℂ) (n : ℕ) :
    jetCoef θ (jetCoef θ c n) 1 = jetCoef θ c (n + 1) := by
  funext p
  simp only [jetCoef, pow_succ]
  ring

/-- The `n`-th derivative of the orbit is the orbit of the `n`-twisted coefficient family. -/
theorem iteratedDeriv_portOrbit (θ : P → ℝ) :
    ∀ (n : ℕ) (c : P → ℂ) (h : Summable fun p => ‖c p‖ ^ 2)
      (hn : ∀ k ≤ n, Summable (fun p => ‖jetCoef θ c k p‖ ^ 2)),
      iteratedDeriv n (portOrbit θ c h) = portOrbit θ (jetCoef θ c n) (hn n le_rfl) := by
  intro n
  induction n with
  | zero =>
      intro c h hn
      rw [iteratedDeriv_zero]
      exact portOrbit_congr (jetCoef_zero_order θ c).symm h _
  | succ n ih =>
      intro c h hn
      have hjn : jetCoef θ (jetCoef θ c n) 1 = jetCoef θ c (n + 1) := jetCoef_jet_one θ c n
      have h1 : Summable (fun p => ‖jetCoef θ (jetCoef θ c n) 1 p‖ ^ 2) := by
        rw [hjn]; exact hn (n + 1) le_rfl
      rw [iteratedDeriv_succ, ih c h fun k hk => hn k (by omega), deriv_portOrbit _ h1]
      exact portOrbit_congr hjn _ _

end Jets

end HTGeometry.ConstraintMotiveRelativity
