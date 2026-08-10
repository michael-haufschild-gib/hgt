import GaloisForLFunctions.HTGeometry.QGammaFiveChart
import GaloisForLFunctions.HTGeometry.MarkedCyclicRigidity
import GaloisForLFunctions.HTGeometry.AbsConvergentPowerSeries

/-!
# The marked GNS chart of the q-Gamma process

The q-Gamma characteristic process is the cyclic matrix coefficient of an explicit diagonal unitary
group on `ℓ²`.  The cyclic vector really is cyclic: a vector orthogonal to the whole orbit produces
an absolutely convergent power series — convergent past the unit circle because `w_n ≤ qⁿ` — which
vanishes on the unit circle, hence identically, so all its coefficients vanish.

Together with the rigidity of marked cyclic presentations this closes the five-chart reconstruction:
parameter, probability law, characteristic process, marked minimal GNS triple, and analytic response
germ determine one another.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

noncomputable section

/-! ## Diagonal unitaries of `ℓ²` -/

/-- Multiplication by a unimodular sequence, as a linear map of `ℓ²`. -/
def lpPhaseLM (d : ℕ → ℂ) (hd : ∀ n, ‖d n‖ = 1) : QGammaSpace →ₗ[ℂ] QGammaSpace :=
  lpDiagLM d (C := 1) fun n => le_of_eq (hd n)

@[simp] theorem lpPhaseLM_apply (d : ℕ → ℂ) (hd : ∀ n, ‖d n‖ = 1) (f : QGammaSpace) (n : ℕ) :
    ((lpPhaseLM d hd f : QGammaSpace) : ℕ → ℂ) n = d n * (f : ℕ → ℂ) n := rfl

theorem norm_lpPhaseLM (d : ℕ → ℂ) (hd : ∀ n, ‖d n‖ = 1) (f : QGammaSpace) :
    ‖lpPhaseLM d hd f‖ = ‖f‖ := by
  have hsq : ‖lpPhaseLM d hd f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [norm_sq_lp, norm_sq_lp]
    refine tsum_congr fun n => ?_
    rw [lpPhaseLM_apply, norm_mul, hd n, one_mul]
  rw [← Real.sqrt_sq (norm_nonneg (lpPhaseLM d hd f)), ← Real.sqrt_sq (norm_nonneg f), hsq]

theorem norm_inv_eq_one {d : ℕ → ℂ} (hd : ∀ n, ‖d n‖ = 1) (n : ℕ) : ‖(d n)⁻¹‖ = 1 := by
  rw [norm_inv, hd n, inv_one]

/-- Multiplication by a unimodular sequence, as a unitary of `ℓ²`. -/
def lpPhaseEquiv (d : ℕ → ℂ) (hd : ∀ n, ‖d n‖ = 1) : QGammaSpace ≃ₗᵢ[ℂ] QGammaSpace where
  toLinearEquiv :=
    LinearEquiv.ofLinear (lpPhaseLM d hd) (lpPhaseLM (fun n => (d n)⁻¹) (norm_inv_eq_one hd))
      (by
        refine LinearMap.ext fun f => lp.ext (funext fun n => ?_)
        have hne : d n ≠ 0 := by
          intro h0
          have hdn := hd n
          rw [h0, norm_zero] at hdn
          exact absurd hdn (by norm_num)
        show d n * ((d n)⁻¹ * (f : ℕ → ℂ) n) = (f : ℕ → ℂ) n
        field_simp)
      (by
        refine LinearMap.ext fun f => lp.ext (funext fun n => ?_)
        have hne : d n ≠ 0 := by
          intro h0
          have hdn := hd n
          rw [h0, norm_zero] at hdn
          exact absurd hdn (by norm_num)
        show (d n)⁻¹ * (d n * (f : ℕ → ℂ) n) = (f : ℕ → ℂ) n
        field_simp)
  norm_map' := norm_lpPhaseLM d hd

@[simp] theorem lpPhaseEquiv_apply (d : ℕ → ℂ) (hd : ∀ n, ‖d n‖ = 1) (f : QGammaSpace) (n : ℕ) :
    ((lpPhaseEquiv d hd f : QGammaSpace) : ℕ → ℂ) n = d n * (f : ℕ → ℂ) n := rfl

/-! ## The q-Gamma unitary group -/

/-- The phase sequence `exp(i t x_n)`. -/
def qPhase (q : RealEulerNome) (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ))

theorem qPhase_norm (q : RealEulerNome) (t : ℝ) (n : ℕ) : ‖qPhase q t n‖ = 1 := by
  rw [qPhase, Complex.norm_exp]
  have hre : (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero]

theorem qPhase_zero (q : RealEulerNome) (n : ℕ) : qPhase q 0 n = 1 := by
  rw [qPhase]
  simp

theorem qPhase_add (q : RealEulerNome) (s t : ℝ) (n : ℕ) :
    qPhase q (s + t) n = qPhase q s n * qPhase q t n := by
  rw [qPhase, qPhase, qPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The q-Gamma unitary group** `U_t = multiplication by exp(i t x_n)`. -/
def qUnitary (q : RealEulerNome) : Multiplicative ℝ →* (QGammaSpace ≃ₗᵢ[ℂ] QGammaSpace) where
  toFun t := lpPhaseEquiv (qPhase q (Multiplicative.toAdd t)) (qPhase_norm q _)
  map_one' := by
    refine LinearIsometryEquiv.ext fun f => lp.ext (funext fun n => ?_)
    show qPhase q (Multiplicative.toAdd (1 : Multiplicative ℝ)) n * (f : ℕ → ℂ) n = (f : ℕ → ℂ) n
    rw [show Multiplicative.toAdd (1 : Multiplicative ℝ) = 0 from rfl, qPhase_zero, one_mul]
  map_mul' s t := by
    refine LinearIsometryEquiv.ext fun f => lp.ext (funext fun n => ?_)
    show qPhase q (Multiplicative.toAdd (s * t)) n * (f : ℕ → ℂ) n
      = qPhase q (Multiplicative.toAdd s) n
        * (qPhase q (Multiplicative.toAdd t) n * (f : ℕ → ℂ) n)
    rw [show Multiplicative.toAdd (s * t)
        = Multiplicative.toAdd s + Multiplicative.toAdd t from rfl, qPhase_add, mul_assoc]

theorem qUnitary_apply (q : RealEulerNome) (t : Multiplicative ℝ) (f : QGammaSpace) (n : ℕ) :
    ((qUnitary q t f : QGammaSpace) : ℕ → ℂ) n
      = qPhase q (Multiplicative.toAdd t) n * (f : ℕ → ℂ) n := rfl

/-- **Equation (4).**  The orbit of the cyclic vector is the q-Gamma orbit. -/
theorem qUnitary_qOmega (q : RealEulerNome) (t : ℝ) :
    qUnitary q (Multiplicative.ofAdd t) (qOmega q) = qOrbit q t := by
  refine lp.ext (funext fun n => ?_)
  rw [qUnitary_apply]
  rfl

theorem range_qUnitary_qOmega (q : RealEulerNome) :
    (Set.range fun t : Multiplicative ℝ => qUnitary q t (qOmega q))
      = Set.range (qOrbit q) := by
  ext v
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.toAdd t, by rw [← qUnitary_qOmega]; rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd t, qUnitary_qOmega q t⟩

/-! ## Cyclicity of the source vector -/

theorem sqrt_qGammaWeight_le (q : RealEulerNome) (n : ℕ) :
    Real.sqrt (qGammaWeight q n) ≤ Real.sqrt q.val ^ n := by
  have h := Real.sqrt_le_sqrt (qGammaWeight_le_pow q n)
  have hpow : Real.sqrt (q.val ^ n) = Real.sqrt q.val ^ n := by
    rw [show q.val ^ n = (Real.sqrt q.val ^ n) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt q.pos.le]]
    exact Real.sqrt_sq (by positivity)
  rwa [hpow] at h

/-- **The GNS source vector is cyclic.**  A vector orthogonal to the whole orbit gives an
absolutely convergent power series, convergent past the unit circle because `w_n ≤ qⁿ`, which
vanishes on the unit circle and therefore has all coefficients zero. -/
theorem dense_span_qOrbit (q : RealEulerNome) :
    Dense ((Submodule.span ℂ (Set.range (qOrbit q)) : Submodule ℂ QGammaSpace)
      : Set QGammaSpace) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro v hv
  -- the orthogonality relations
  have horth : ∀ t : ℝ, (inner ℂ (qOrbit q t) v : ℂ) = 0 := fun t =>
    (Submodule.mem_orthogonal _ v).mp hv _ (Submodule.subset_span ⟨t, rfl⟩)
  set a : ℕ → ℂ := fun n => ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ) * (v : ℕ → ℂ) n with ha
  -- the geometric radius
  set s : ℝ := Real.sqrt q.val with hs
  set u : ℝ := Real.sqrt s with hu
  have hs0 : 0 < s := Real.sqrt_pos.mpr q.pos
  have hs1 : s < 1 := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt q.pos.le q.lt_one
  have hu0 : 0 < u := Real.sqrt_pos.mpr hs0
  have hu1 : u < 1 := by
    rw [hu, show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt hs0.le hs1
  have husq : u ^ 2 = s := Real.sq_sqrt hs0.le
  set ρ : NNReal := ⟨u⁻¹, le_of_lt (inv_pos.mpr hu0)⟩ with hρ
  have hρ1 : (1 : NNReal) < ρ := by
    rw [← NNReal.coe_lt_coe]
    show (1 : ℝ) < u⁻¹
    rw [lt_inv_comm₀ one_pos hu0, inv_one]
    exact hu1
  -- the coefficient bound
  have hbound : ∀ n : ℕ, ‖a n‖ * (ρ : ℝ) ^ n ≤ ‖v‖ * u ^ n := by
    intro n
    have hvn : ‖(v : ℕ → ℂ) n‖ ≤ ‖v‖ := lp.norm_apply_le_norm (by norm_num) v n
    have hsq : ‖a n‖ ≤ ‖v‖ * s ^ n := by
      rw [ha]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      calc Real.sqrt (qGammaWeight q n) * ‖(v : ℕ → ℂ) n‖
          ≤ s ^ n * ‖v‖ :=
            mul_le_mul (sqrt_qGammaWeight_le q n) hvn (norm_nonneg _) (by positivity)
        _ = ‖v‖ * s ^ n := by ring
    have hpow : (ρ : ℝ) ^ n = (u ^ n)⁻¹ := by
      show (u⁻¹ : ℝ) ^ n = (u ^ n)⁻¹
      rw [inv_pow]
    rw [hpow]
    have hun : (0 : ℝ) < u ^ n := pow_pos hu0 n
    rw [← husq, ← pow_mul, mul_comm 2 n, pow_mul] at hsq
    calc ‖a n‖ * (u ^ n)⁻¹ ≤ (‖v‖ * (u ^ n) ^ 2) * (u ^ n)⁻¹ := by
          exact mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = ‖v‖ * u ^ n := by field_simp
  have hsummable : Summable fun n : ℕ => ‖a n‖ * (ρ : ℝ) ^ n := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) hbound ?_
    exact (summable_geometric_of_lt_one hu0.le hu1).mul_left ‖v‖
  -- the power series vanishes on the unit circle
  have hcirc : ∀ θ : ℝ, ∑' n : ℕ, a n * Complex.exp (Complex.I * (θ : ℂ)) ^ n = 0 := by
    intro θ
    have hlog : Real.log q.val ≠ 0 := ne_of_lt (Real.log_neg q.pos q.lt_one)
    set t : ℝ := -θ / Real.log q.val with ht
    have hphase : -t * Real.log q.val = θ := by
      rw [ht]
      field_simp
    set c : ℂ := Complex.exp (Complex.I * ((t * Real.log (1 - q.val) : ℝ) : ℂ)) with hc
    have hE : ∀ n : ℕ,
        Complex.I * ((t * Real.log (1 - q.val) : ℝ) : ℂ)
            + (n : ℂ) * (Complex.I * ((θ : ℝ) : ℂ))
          = -(Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)) := by
      intro n
      rw [qGammaAtom, ← hphase]
      push_cast
      ring
    have hconj : ∀ n : ℕ, (starRingEnd ℂ) ((qOrbit q t : ℕ → ℂ) n)
        = Complex.exp (-(Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)))
          * ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ) := by
      intro n
      rw [qOrbit_apply, map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
      congr 2
      simp
    have hkey : ∀ n : ℕ,
        (starRingEnd ℂ) ((qOrbit q t : ℕ → ℂ) n) * (v : ℕ → ℂ) n
          = c * (a n * Complex.exp (Complex.I * (θ : ℂ)) ^ n) := by
      intro n
      have hpow : Complex.exp (Complex.I * ((θ : ℝ) : ℂ)) ^ n
          = Complex.exp ((n : ℂ) * (Complex.I * ((θ : ℝ) : ℂ))) :=
        (Complex.exp_nat_mul _ n).symm
      rw [hconj n, hpow]
      simp only [ha, hc]
      rw [← hE n, Complex.exp_add]
      ring
    have hinner := horth t
    rw [lp.inner_eq_tsum] at hinner
    have hinner' : ∑' n : ℕ, (starRingEnd ℂ) ((qOrbit q t : ℕ → ℂ) n) * (v : ℕ → ℂ) n = 0 := by
      rw [← hinner]
      refine tsum_congr fun n => ?_
      rw [RCLike.inner_apply]
      ring
    have hexpand : ∑' n : ℕ, (starRingEnd ℂ) ((qOrbit q t : ℕ → ℂ) n) * (v : ℕ → ℂ) n
        = c * ∑' n : ℕ, a n * Complex.exp (Complex.I * (θ : ℂ)) ^ n := by
      rw [← tsum_mul_left]
      exact tsum_congr hkey
    rw [hexpand] at hinner'
    have hcne : c ≠ 0 := by
      rw [hc]
      exact Complex.exp_ne_zero _
    exact (mul_eq_zero.mp hinner').resolve_left hcne
  -- hence every coefficient vanishes
  have hzero := powerCoeff_eq_zero_of_circle hρ1 hsummable hcirc
  refine lp.ext (funext fun n => ?_)
  have hn := hzero n
  rw [ha] at hn
  have hsqrt : ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (qGammaWeight_pos q n))
  have := (mul_eq_zero.mp hn).resolve_left hsqrt
  rw [this]
  rfl

theorem dense_span_qUnitary_qOmega (q : RealEulerNome) :
    Dense ((Submodule.span ℂ
        (Set.range fun t : Multiplicative ℝ => qUnitary q t (qOmega q))
        : Submodule ℂ QGammaSpace) : Set QGammaSpace) := by
  rw [range_qUnitary_qOmega]
  exact dense_span_qOrbit q

/-! ## The marked GNS chart -/

/-- Marked equivalence of the two q-Gamma GNS presentations. -/
def MarkedEquivalent (q q' : RealEulerNome) : Prop :=
  ∃ V : QGammaSpace ≃ₗᵢ[ℂ] QGammaSpace, V (qOmega q) = qOmega q' ∧
    ∀ (t : Multiplicative ℝ) (x : QGammaSpace), V (qUnitary q t x) = qUnitary q' t (V x)

theorem qChar_eq_inner_qUnitary (q : RealEulerNome) (t : Multiplicative ℝ) :
    (inner ℂ (qOmega q) (qUnitary q t (qOmega q)) : ℂ) = qChar q (Multiplicative.toAdd t) := by
  rw [show qUnitary q t (qOmega q) = qOrbit q (Multiplicative.toAdd t) from by
    rw [← qUnitary_qOmega q (Multiplicative.toAdd t)]; rfl]
  exact (qChar_eq_inner q (Multiplicative.toAdd t)).symm

/-- **Chart 4 determines the characteristic process.** -/
theorem qChar_eq_of_markedEquivalent {q q' : RealEulerNome} (h : MarkedEquivalent q q') :
    qChar q = qChar q' := by
  obtain ⟨V, hVΩ, hVint⟩ := h
  funext t
  have h1 := qChar_eq_inner_qUnitary q (Multiplicative.ofAdd t)
  have h2 := qChar_eq_inner_qUnitary q' (Multiplicative.ofAdd t)
  have h3 : (inner ℂ (qOmega q) (qUnitary q (Multiplicative.ofAdd t) (qOmega q)) : ℂ)
      = inner ℂ (qOmega q') (qUnitary q' (Multiplicative.ofAdd t) (qOmega q')) := by
    rw [← V.inner_map_map (qOmega q) (qUnitary q (Multiplicative.ofAdd t) (qOmega q)),
      hVint, hVΩ]
  rw [show Multiplicative.toAdd (Multiplicative.ofAdd t) = t from rfl] at h1 h2
  rw [← h1, ← h2, h3]

/-- **Chart 3 determines chart 4**: equal characteristic processes force a marked unitary
equivalence, by the rigidity of marked cyclic presentations. -/
theorem markedEquivalent_of_qChar_eq {q q' : RealEulerNome} (h : qChar q = qChar q') :
    MarkedEquivalent q q' := by
  have hcoef : ∀ t : Multiplicative ℝ,
      (inner ℂ (qOmega q) (qUnitary q t (qOmega q)) : ℂ)
        = inner ℂ (qOmega q') (qUnitary q' t (qOmega q')) := by
    intro t
    rw [qChar_eq_inner_qUnitary, qChar_eq_inner_qUnitary, h]
  obtain ⟨V, hV, -⟩ := exists_unique_marked_intertwiner (qUnitary q) (qUnitary q')
    (qOmega q) (qOmega q') (dense_span_qUnitary_qOmega q) (dense_span_qUnitary_qOmega q') hcoef
  exact ⟨V, hV.1, hV.2⟩

/-! ## Five-chart rigidity -/

/-- **Corollary 4.1.**  Parameter, probability law, characteristic process, marked minimal GNS
triple, and analytic response germ determine one another. -/
theorem qGamma_fiveChart_tfae (q q' : RealEulerNome) :
    List.TFAE
      [q = q',
       qLaw q = qLaw q',
       qChar q = qChar q',
       MarkedEquivalent q q',
       qResponseFun q =ᶠ[𝓝 0] qResponseFun q'] := by
  tfae_have 1 → 2 := fun h => by rw [h]
  tfae_have 2 → 3 := fun h => nome_eq_of_qLaw_eq h ▸ rfl
  tfae_have 3 → 4 := fun h => markedEquivalent_of_qChar_eq h
  tfae_have 4 → 5 := fun h => nome_eq_of_qChar_eq (qChar_eq_of_markedEquivalent h) ▸
    EventuallyEq.rfl
  tfae_have 5 → 1 := fun h => nome_eq_of_response_germ_eq h
  tfae_finish

/-! ## Invariance of the reconstructed data -/

/-- **Corollary 5.1.**  Every quantity reconstructed from the nome is invariant under marked
process equivalence: the atoms, the weights, the moments, the tilted law, and the withheld tilt
response of equation (14). -/
theorem markedEquivalent_invariance {q q' : RealEulerNome} (h : MarkedEquivalent q q') :
    q = q' ∧ qGammaAtom q = qGammaAtom q' ∧ qGammaWeight q = qGammaWeight q'
      ∧ qMoment q = qMoment q' ∧ qTiltWeight q = qTiltWeight q' ∧ qLaw q = qLaw q'
      ∧ qResponseFun q = qResponseFun q' := by
  have hq : q = q' := nome_eq_of_qChar_eq (qChar_eq_of_markedEquivalent h)
  subst hq
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

end GaloisForLFunctions.HTGeometry
