import GaloisForLFunctions.HTGeometry.IsometricRecurrence
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Vanishing from a relatively compact translation orbit

Translation acts isometrically on bounded continuous functions in the supremum metric.  If the
translation orbit of `f` has compact closure — **Bochner's criterion** for almost periodicity — then
`f` returns to itself arbitrarily far out, so `f` cannot decay unless it is identically zero.

This is the form of the vanishing lemma that survives the passage from finite exponential sums to
absolutely convergent generalized Dirichlet series.  The Bohr formulation (relatively dense
`ε`-almost-periods) requires Kronecker's theorem to verify for a trigonometric polynomial; the
Bochner formulation requires only total boundedness of the orbit, which passes to uniform limits.
-/

open Filter Metric BoundedContinuousFunction

namespace HTGeometry

variable {E : Type*} [NormedAddCommGroup E]

/-- Translation of bounded continuous functions on `ℝ`. -/
noncomputable def translate (t : ℝ) (f : BoundedContinuousFunction ℝ E) :
    BoundedContinuousFunction ℝ E :=
  f.compContinuous ⟨fun x => x + t, by continuity⟩

@[simp] theorem translate_apply (t : ℝ) (f : BoundedContinuousFunction ℝ E) (x : ℝ) :
    translate t f x = f (x + t) := rfl

/-- Translation is an isometric additive `ℝ`-action on bounded continuous functions. -/
noncomputable def translationAction (E : Type*) [NormedAddCommGroup E] :
    GaloisForLFunctions.IsometricRAction (BoundedContinuousFunction ℝ E) where
  act := translate
  map_add := by
    intro s t f
    ext x
    simp [translate_apply]
    ring_nf
  isometry := by
    intro t
    refine Isometry.of_dist_eq fun f g => ?_
    rw [dist_eq_iSup, dist_eq_iSup]
    exact (Equiv.addRight t).iSup_congr fun x => by simp [translate_apply]

/-- **Vanishing from recurrence.**  A bounded continuous function whose translation orbit has
compact closure and which tends to zero at `+∞` is identically zero. -/
theorem eq_zero_of_compact_orbit_of_tendsto_zero
    (f : BoundedContinuousFunction ℝ E)
    (hcompact : IsCompact (closure (Set.range
      (fun t : ℝ => (translationAction E).act t f))))
    (h0 : Tendsto (fun x : ℝ => f x) atTop (nhds 0)) :
    ∀ x, f x = 0 := by
  intro x₀
  have key : ∀ ε : ℝ, 0 < ε → ‖f x₀‖ ≤ 2 * ε := by
    intro ε hε
    -- the limit gives a threshold beyond which `‖f‖ ≤ ε`
    have hnorm : Tendsto (fun x : ℝ => ‖f x‖) atTop (nhds 0) := by
      simpa using (continuous_norm (E := E)).tendsto (0 : E) |>.comp h0
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hnorm.eventually_le_const hε)
    -- recurrence supplies a return time beyond `M - x₀`
    obtain ⟨t, ht, hdist⟩ :=
      GaloisForLFunctions.isometricAction_recurrence (translationAction E) hcompact hε (M - x₀ + 1)
    have hx : M ≤ x₀ + t := by linarith
    have hpt : ‖f (x₀ + t) - f x₀‖ ≤ ε := by
      have := BoundedContinuousFunction.dist_coe_le_dist (f := (translationAction E).act t f)
        (g := f) x₀
      rw [← dist_eq_norm]
      calc dist (f (x₀ + t)) (f x₀)
          = dist ((translationAction E).act t f x₀) (f x₀) := rfl
        _ ≤ dist ((translationAction E).act t f) f := this
        _ ≤ ε := hdist.le
    calc ‖f x₀‖ = ‖f (x₀ + t) - (f (x₀ + t) - f x₀)‖ := by congr 1; abel
      _ ≤ ‖f (x₀ + t)‖ + ‖f (x₀ + t) - f x₀‖ := norm_sub_le _ _
      _ ≤ ε + ε := add_le_add (hM _ hx) hpt
      _ = 2 * ε := by ring
  by_contra hne
  have hpos : 0 < ‖f x₀‖ := norm_pos_iff.mpr hne
  have := key (‖f x₀‖ / 4) (by positivity)
  linarith

/-- The translation orbit of a function. -/
def translationOrbit (f : BoundedContinuousFunction ℝ E) : Set (BoundedContinuousFunction ℝ E) :=
  Set.range fun t : ℝ => translate t f

theorem dist_translate (t : ℝ) (f g : BoundedContinuousFunction ℝ E) :
    dist (translate t f) (translate t g) = dist f g :=
  (translationAction E).isometry t |>.dist_eq f g

/-- **Bochner's criterion passes to uniform limits.**  If `f` is uniformly approximable by functions
with totally bounded translation orbits, its own orbit is totally bounded.  This is the step that
carries the finite exponential-sum case to absolutely convergent Dirichlet series, and it is exactly
what the Bohr formulation cannot do without Kronecker. -/
theorem totallyBounded_translationOrbit_of_uniform_approx
    {f : BoundedContinuousFunction ℝ E}
    (h : ∀ ε : ℝ, 0 < ε → ∃ g : BoundedContinuousFunction ℝ E,
      TotallyBounded (translationOrbit g) ∧ dist f g ≤ ε) :
    TotallyBounded (translationOrbit f) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨g, hgTB, hclose⟩ := h (ε / 3) (by linarith)
  rw [Metric.totallyBounded_iff] at hgTB
  obtain ⟨F, hFfin, hFcov⟩ := hgTB (ε / 3) (by linarith)
  refine ⟨F, hFfin, ?_⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨y, hyF, hy⟩ := Set.mem_iUnion₂.mp (hFcov ⟨t, rfl⟩)
  refine Set.mem_iUnion₂.mpr ⟨y, hyF, ?_⟩
  have hstep : dist (translate t f) (translate t g) ≤ ε / 3 := by
    rw [dist_translate]; exact hclose
  calc dist (translate t f) y
      ≤ dist (translate t f) (translate t g) + dist (translate t g) y := dist_triangle _ _ _
    _ < ε / 3 + ε / 3 := by
        exact add_lt_add_of_le_of_lt hstep (Metric.mem_ball.mp hy)
    _ < ε := by linarith

/-- **Separation of an almost-periodic part from a decaying part.**  If a function with totally
bounded translation orbit is cancelled by a function decaying at `+∞`, both vanish.

This is the abstract mechanism behind stratifying a differential relation by the decay rate of its
archimedean factors: the stratum carrying no decay is almost periodic, every other stratum decays,
and the two cannot cancel. -/
theorem eq_zero_of_totallyBounded_orbit_of_add_tendsto_zero [CompleteSpace E]
    (f : BoundedContinuousFunction ℝ E)
    (hTB : TotallyBounded (translationOrbit f))
    (h : ℝ → E) (hdecay : Tendsto h atTop (nhds 0))
    (hsum : ∀ x, f x + h x = 0) :
    ∀ x, f x = 0 := by
  have hfdecay : Tendsto (fun x : ℝ => f x) atTop (nhds 0) := by
    have hfe : ∀ x : ℝ, f x = -h x := by
      intro x
      have hx := hsum x
      exact eq_neg_of_add_eq_zero_left hx
    have : Tendsto (fun x : ℝ => -h x) atTop (nhds 0) := by
      simpa using hdecay.neg
    exact this.congr fun x => (hfe x).symm
  refine eq_zero_of_compact_orbit_of_tendsto_zero f ?_ hfdecay
  exact TotallyBounded.isCompact_of_isClosed hTB.closure isClosed_closure

section FiniteSums

/-- The unit-modulus character with real frequency, as a bounded continuous function. -/
noncomputable def cisBCF (l : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : ℝ => Complex.exp (Complex.I * ((l * t : ℝ) : ℂ)))
    (by fun_prop) 1
    (by
      intro t
      rw [Complex.norm_exp]
      have h : (Complex.I * ((l * t : ℝ) : ℂ)).re = 0 := by simp [Complex.mul_re]
      rw [h, Real.exp_zero])

@[simp] theorem cisBCF_apply (l t : ℝ) :
    cisBCF l t = Complex.exp (Complex.I * ((l * t : ℝ) : ℂ)) := by
  rfl

theorem norm_cisBCF_apply (l t : ℝ) : ‖cisBCF l t‖ = 1 := by
  rw [cisBCF_apply, Complex.norm_exp]
  have h : (Complex.I * ((l * t : ℝ) : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [h, Real.exp_zero]

/-- **The translation orbit of a finite exponential sum is totally bounded.**  Translating only
rotates the coefficients, so the orbit lies inside the continuous image of a product of closed
discs.  Only *compactness* of that product is used -- no density statement, hence no Kronecker
theorem. -/
theorem totallyBounded_translationOrbit_expSum {n : ℕ} (lam : Fin n → ℝ) (b : Fin n → ℂ) :
    TotallyBounded (translationOrbit (∑ i, b i • cisBCF (lam i))) := by
  classical
  set Φ : (Fin n → ℂ) → BoundedContinuousFunction ℝ ℂ :=
    fun c => ∑ i, c i • cisBCF (lam i) with hΦ
  have hcont : Continuous Φ := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_apply i).smul continuous_const
  set K : Set (Fin n → ℂ) := Set.pi Set.univ (fun i => Metric.closedBall 0 ‖b i‖) with hK
  have hKcompact : IsCompact K :=
    isCompact_univ_pi fun i => isCompact_closedBall 0 ‖b i‖
  have hsub : translationOrbit (∑ i, b i • cisBCF (lam i)) ⊆ Φ '' K := by
    rintro _ ⟨u, rfl⟩
    refine ⟨fun i => Complex.exp (Complex.I * ((lam i * u : ℝ) : ℂ)) * b i, ?_, ?_⟩
    · intro i _
      simp only [Metric.mem_closedBall, dist_zero_right, norm_mul]
      have h1 : ‖Complex.exp (Complex.I * ((lam i * u : ℝ) : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        have h : (Complex.I * ((lam i * u : ℝ) : ℂ)).re = 0 := by simp [Complex.mul_re]
        rw [h, Real.exp_zero]
      rw [h1, one_mul]
    · ext t
      simp only [hΦ, translate_apply, BoundedContinuousFunction.coe_sum, Finset.sum_apply,
        BoundedContinuousFunction.smul_apply, smul_eq_mul, cisBCF_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm (Complex.exp (Complex.I * ((lam i * u : ℝ) : ℂ))) (b i), mul_assoc,
        ← Complex.exp_add]
      congr 2
      push_cast
      ring
  exact (hKcompact.image hcont).totallyBounded.subset hsub

/-- **An absolutely convergent exponential series has totally bounded translation orbit.**  Its
partial sums are finite exponential sums, whose orbits are totally bounded, and they converge
uniformly; total boundedness passes to the limit.

Applied to a Dirichlet series on a vertical line -- where the frequencies are `-log n` and absolute
convergence holds for `Re s > 1` -- this makes every jet of the series almost periodic in the sense
needed for the decay/almost-periodic separation. -/
theorem totallyBounded_translationOrbit_tsum
    (lam : ℕ → ℝ) (b : ℕ → ℂ) (hb : Summable fun n => ‖b n‖) :
    TotallyBounded (translationOrbit (∑' n, b n • cisBCF (lam n))) := by
  classical
  have hnorm : ∀ n : ℕ, ‖b n • cisBCF (lam n)‖ ≤ ‖b n‖ := by
    intro n
    rw [norm_smul]
    have : ‖cisBCF (lam n)‖ ≤ 1 := by
      refine BoundedContinuousFunction.norm_le_of_nonempty.mpr fun t => ?_
      rw [norm_cisBCF_apply]
    calc ‖b n‖ * ‖cisBCF (lam n)‖ ≤ ‖b n‖ * 1 :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖b n‖ := mul_one _
  have hsummable : Summable fun n => b n • cisBCF (lam n) :=
    Summable.of_norm_bounded hb hnorm
  refine totallyBounded_translationOrbit_of_uniform_approx fun ε hε => ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hsummable.hasSum.tendsto_sum_nat ε hε
  refine ⟨∑ n ∈ Finset.range N, b n • cisBCF (lam n), ?_, ?_⟩
  · have hrange : (∑ n ∈ Finset.range N, b n • cisBCF (lam n))
        = ∑ i : Fin N, b (i : ℕ) • cisBCF (lam (i : ℕ)) :=
      (Fin.sum_univ_eq_sum_range (fun n => b n • cisBCF (lam n)) N).symm
    rw [hrange]
    exact totallyBounded_translationOrbit_expSum (fun i : Fin N => lam (i : ℕ))
      (fun i : Fin N => b (i : ℕ))
  · rw [dist_comm]
    exact (hN N le_rfl).le

/-- Translation is multiplicative on complex-valued bounded continuous functions. -/
theorem translate_mul (t : ℝ) (f g : BoundedContinuousFunction ℝ ℂ) :
    translate t (f * g) = translate t f * translate t g := by
  ext x
  simp [translate_apply]

/-- **Totally bounded translation orbits are closed under products.**  The orbit of a product lies
in the image of the product of the two orbit closures under multiplication, which is compact.

This is what allows monomials in the jets of a Dirichlet series to be treated as almost periodic. -/
theorem totallyBounded_translationOrbit_mul (f g : BoundedContinuousFunction ℝ ℂ)
    (hf : TotallyBounded (translationOrbit f)) (hg : TotallyBounded (translationOrbit g)) :
    TotallyBounded (translationOrbit (f * g)) := by
  have hfc : IsCompact (closure (translationOrbit f)) :=
    TotallyBounded.isCompact_of_isClosed hf.closure isClosed_closure
  have hgc : IsCompact (closure (translationOrbit g)) :=
    TotallyBounded.isCompact_of_isClosed hg.closure isClosed_closure
  have hprod : IsCompact ((closure (translationOrbit f)) ×ˢ (closure (translationOrbit g))) :=
    hfc.prod hgc
  have hmul : Continuous fun p : BoundedContinuousFunction ℝ ℂ ×
      BoundedContinuousFunction ℝ ℂ => p.1 * p.2 := continuous_mul
  have himage : IsCompact ((fun p : BoundedContinuousFunction ℝ ℂ ×
      BoundedContinuousFunction ℝ ℂ => p.1 * p.2) ''
      ((closure (translationOrbit f)) ×ˢ (closure (translationOrbit g)))) :=
    hprod.image hmul
  refine himage.totallyBounded.subset ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨(translate t f, translate t g),
    ⟨subset_closure ⟨t, rfl⟩, subset_closure ⟨t, rfl⟩⟩, (translate_mul t f g).symm⟩

end FiniteSums

end HTGeometry
