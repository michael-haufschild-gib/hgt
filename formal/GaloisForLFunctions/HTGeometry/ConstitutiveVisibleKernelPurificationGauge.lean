import Mathlib

/-!
# Hidden-history elimination, the visible positive kernel, and the purification gauge

Eliminating a hidden factor from a pure amplitude produces the Gram kernel of its columns.  That
kernel is positive semidefinite with unit trace, its rank is the Schmidt rank of the amplitude, it
is rank one exactly for a separable amplitude, and it reproduces every visible expectation.  A
maximally entangled amplitude therefore leaves a kernel of full rank, so a history theory closed
under discarding hidden factors cannot stay inside rank-one amplitudes.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Finset

open scoped ComplexOrder

section VisibleKernel

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The visible kernel obtained by eliminating the hidden `A`-history, equation (1). -/
def visibleKernel (Ψ : Matrix A B ℂ) : Matrix B B ℂ :=
  Matrix.of fun b b' => ∑ a, Ψ a b * (starRingEnd ℂ) (Ψ a b')

omit [Fintype B] in
theorem visibleKernel_apply (Ψ : Matrix A B ℂ) (b b' : B) :
    visibleKernel Ψ b b' = ∑ a, Ψ a b * (starRingEnd ℂ) (Ψ a b') := rfl

omit [Fintype B] in
/-- The visible kernel is the transpose of the Gram matrix of the columns. -/
theorem visibleKernel_eq_transpose (Ψ : Matrix A B ℂ) :
    visibleKernel Ψ = (Ψᴴ * Ψ)ᵀ := by
  ext b b'
  rw [Matrix.transpose_apply, Matrix.mul_apply, visibleKernel_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.conjTranspose_apply]
  show Ψ a b * (starRingEnd ℂ) (Ψ a b') = (starRingEnd ℂ) (Ψ a b') * Ψ a b
  ring

/-- **Clause 1, positivity.** -/
theorem visibleKernel_posSemidef (Ψ : Matrix A B ℂ) : (visibleKernel Ψ).PosSemidef := by
  rw [visibleKernel_eq_transpose]
  exact (Matrix.posSemidef_conjTranspose_mul_self Ψ).transpose

/-- **Clause 1, trace.** -/
theorem trace_visibleKernel (Ψ : Matrix A B ℂ) :
    (visibleKernel Ψ).trace = ((∑ a, ∑ b, ‖Ψ a b‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace]
  have hterm : ∀ b : B, (visibleKernel Ψ).diag b = ∑ a, ((‖Ψ a b‖ ^ 2 : ℝ) : ℂ) := by
    intro b
    rw [Matrix.diag_apply, visibleKernel_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_comm]
  push_cast
  rfl

/-- **Clause 2, equation (2).**  The kernel rank is the Schmidt rank of the amplitude. -/
theorem rank_visibleKernel [DecidableEq B] (Ψ : Matrix A B ℂ) :
    (visibleKernel Ψ).rank = Ψ.rank := by
  rw [visibleKernel_eq_transpose, Matrix.rank_transpose, Matrix.rank_conjTranspose_mul_self]

/-- **Clause 4, equation (4).**  Every visible expectation is a trace against the kernel. -/
theorem trace_visibleKernel_mul (Ψ : Matrix A B ℂ) (X : Matrix B B ℂ) :
    (visibleKernel Ψ * X).trace
      = ∑ a, ∑ b, ∑ b', (starRingEnd ℂ) (Ψ a b) * X b b' * Ψ a b' := by
  calc (visibleKernel Ψ * X).trace
      = ∑ b', ∑ b, ∑ a, Ψ a b' * (starRingEnd ℂ) (Ψ a b) * X b b' := by
        rw [Matrix.trace]
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [Matrix.diag_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [visibleKernel_apply, Finset.sum_mul]
    _ = ∑ b, ∑ b', ∑ a, Ψ a b' * (starRingEnd ℂ) (Ψ a b) * X b b' := Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ b', Ψ a b' * (starRingEnd ℂ) (Ψ a b) * X b b' :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ b', Ψ a b' * (starRingEnd ℂ) (Ψ a b) * X b b' := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ b', (starRingEnd ℂ) (Ψ a b) * X b b' * Ψ a b' :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun b' _ => by ring

/-! ### Clause 3 — rank one is separability -/

omit [Fintype A] in
/-- A matrix has rank at most one exactly when it is an outer product. -/
theorem rank_le_one_iff_vecMulVec [DecidableEq B] (Ψ : Matrix A B ℂ) :
    Ψ.rank ≤ 1 ↔ ∃ (α : A → ℂ) (β : B → ℂ), Ψ = Matrix.vecMulVec α β := by
  constructor
  · intro h
    have hprin : (LinearMap.range Ψ.mulVecLin).IsPrincipal :=
      (Submodule.finrank_le_one_iff_isPrincipal _).mp h
    obtain ⟨α, hα⟩ := hprin
    have hcol : ∀ b : B, ∃ c : ℂ, (fun a => Ψ a b) = c • α := by
      intro b
      have hmem : (fun a => Ψ a b) ∈ LinearMap.range Ψ.mulVecLin := by
        refine ⟨Pi.single b 1, ?_⟩
        funext a
        show Ψ.mulVec (Pi.single b 1) a = Ψ a b
        rw [Matrix.mulVec, dotProduct]
        rw [Finset.sum_eq_single b]
        · simp
        · intro b' _ hb'
          rw [Pi.single_eq_of_ne hb', mul_zero]
        · intro hb
          exact absurd (Finset.mem_univ b) hb
      rw [hα, Submodule.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      exact ⟨c, hc.symm⟩
    choose β hβ using hcol
    refine ⟨α, β, ?_⟩
    ext a b
    have := congrFun (hβ b) a
    rw [Matrix.vecMulVec_apply, this]
    show β b * α a = α a * β b
    ring
  · rintro ⟨α, β, rfl⟩
    have hle : LinearMap.range (Matrix.vecMulVec α β).mulVecLin ≤ Submodule.span ℂ {α} := by
      rintro x ⟨v, rfl⟩
      refine Submodule.mem_span_singleton.mpr ⟨∑ b, β b * v b, ?_⟩
      funext a
      show (∑ b, β b * v b) * α a = (Matrix.vecMulVec α β).mulVec v a
      rw [Matrix.mulVec, dotProduct, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.vecMulVec_apply]
      ring
    have hspan : Module.finrank ℂ (Submodule.span ℂ ({α} : Set (A → ℂ))) ≤ 1 :=
      (Submodule.finrank_le_one_iff_isPrincipal _).mpr ⟨α, rfl⟩
    exact le_trans (Submodule.finrank_mono hle) hspan

/-- **Clause 3.**  The visible kernel has rank at most one exactly when the amplitude is
separable. -/
theorem rank_visibleKernel_le_one_iff_separable [DecidableEq B] (Ψ : Matrix A B ℂ) :
    (visibleKernel Ψ).rank ≤ 1 ↔ ∃ (α : A → ℂ) (β : B → ℂ), Ψ = Matrix.vecMulVec α β := by
  rw [rank_visibleKernel, rank_le_one_iff_vecMulVec]

end VisibleKernel

/-! ## §2 — the maximally entangled amplitude -/

section BellObstruction

variable {d : ℕ}

/-- The maximally entangled amplitude matrix `Φ_d`. -/
noncomputable def bellAmp (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  ((1 / Real.sqrt d : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)

/-- **Equation (5).**  Eliminating the hidden factor of the maximally entangled amplitude leaves the
maximally mixed kernel. -/
theorem visibleKernel_bellAmp (hd : 0 < d) :
    visibleKernel (bellAmp d) = ((1 / d : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  ext b b'
  rw [visibleKernel_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hterm : ∀ a : Fin d, bellAmp d a b * (starRingEnd ℂ) (bellAmp d a b')
      = ((1 / d : ℝ) : ℂ) * ((1 : Matrix (Fin d) (Fin d) ℂ) a b
        * (starRingEnd ℂ) ((1 : Matrix (Fin d) (Fin d) ℂ) a b')) := by
    intro a
    rw [bellAmp, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
      Complex.conj_ofReal]
    have hR : (1 / Real.sqrt d : ℝ) * (1 / Real.sqrt d) = 1 / d := by
      rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by positivity)]
    have hsq : ((1 / Real.sqrt d : ℝ) : ℂ) * ((1 / Real.sqrt d : ℝ) : ℂ)
        = ((1 / d : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hR]
    calc ((1 / Real.sqrt d : ℝ) : ℂ) * (1 : Matrix (Fin d) (Fin d) ℂ) a b
          * (((1 / Real.sqrt d : ℝ) : ℂ) * (starRingEnd ℂ) ((1 : Matrix (Fin d) (Fin d) ℂ) a b'))
        = (((1 / Real.sqrt d : ℝ) : ℂ) * ((1 / Real.sqrt d : ℝ) : ℂ))
            * ((1 : Matrix (Fin d) (Fin d) ℂ) a b
              * (starRingEnd ℂ) ((1 : Matrix (Fin d) (Fin d) ℂ) a b')) := by ring
      _ = _ := by rw [hsq]
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum]
  congr 1
  by_cases h : b = b'
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single b]
    · simp
    · intro a _ ha
      simp only [Matrix.one_apply]
      rw [if_neg ha, zero_mul]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun a _ => ?_
    simp only [Matrix.one_apply]
    by_cases h1 : a = b
    · rw [if_pos h1, if_neg (by rw [h1]; exact h), map_zero, mul_zero]
    · rw [if_neg h1, zero_mul]

/-- **The Bell obstruction.**  The visible kernel of the maximally entangled amplitude has full
rank, so for `d ≥ 2` it is not a rank-one projective amplitude. -/
theorem rank_visibleKernel_bellAmp (hd : 0 < d) :
    (visibleKernel (bellAmp d)).rank = d := by
  rw [visibleKernel_bellAmp hd]
  have hne : ((1 / d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 1 / d := by positivity
    simpa using ne_of_gt this
  have hunit : IsUnit (((1 / d : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero).mpr (pow_ne_zero _ hne)
  rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]

theorem bellAmp_not_separable (hd : 2 ≤ d) :
    ¬ (visibleKernel (bellAmp d)).rank ≤ 1 := by
  rw [rank_visibleKernel_bellAmp (by omega)]
  omega

end BellObstruction

/-! ## §3 — a positive diagonal does not determine coherence -/

section CoherenceHidden

/-- The rank-one kernel of a visible amplitude. -/
def rankOneKernel {B : Type*} (β : B → ℂ) : Matrix B B ℂ :=
  Matrix.of fun b b' => β b * (starRingEnd ℂ) (β b')

/-- The balanced coherent amplitude with relative phase `θ`. -/
noncomputable def coherentBeta (θ : ℝ) : Fin 2 → ℂ :=
  ![((1 / Real.sqrt 2 : ℝ) : ℂ),
    Complex.exp (Complex.I * (θ : ℂ)) * ((1 / Real.sqrt 2 : ℝ) : ℂ)]

theorem sqrt_two_sq : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)
    = ((1 / 2 : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]

/-- **The visible probability law is the same for every relative phase.** -/
theorem diag_coherentBeta (θ : ℝ) (b : Fin 2) :
    (rankOneKernel (coherentBeta θ)).diag b = ((1 / 2 : ℝ) : ℂ) := by
  rw [Matrix.diag_apply]
  show coherentBeta θ b * (starRingEnd ℂ) (coherentBeta θ b) = _
  fin_cases b
  · show ((1 / Real.sqrt 2 : ℝ) : ℂ) * (starRingEnd ℂ) ((1 / Real.sqrt 2 : ℝ) : ℂ) = _
    rw [Complex.conj_ofReal, sqrt_two_sq]
  · show (Complex.exp (Complex.I * (θ : ℂ)) * ((1 / Real.sqrt 2 : ℝ) : ℂ))
      * (starRingEnd ℂ) (Complex.exp (Complex.I * (θ : ℂ)) * ((1 / Real.sqrt 2 : ℝ) : ℂ)) = _
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    have hc : (starRingEnd ℂ) (Complex.I * (θ : ℂ)) = -(Complex.I * (θ : ℂ)) := by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hc]
    have hexp : Complex.exp (Complex.I * (θ : ℂ)) * Complex.exp (-(Complex.I * (θ : ℂ))) = 1 := by
      rw [← Complex.exp_add]
      simp
    calc Complex.exp (Complex.I * (θ : ℂ)) * ((1 / Real.sqrt 2 : ℝ) : ℂ)
        * (Complex.exp (-(Complex.I * (θ : ℂ))) * ((1 / Real.sqrt 2 : ℝ) : ℂ))
        = (Complex.exp (Complex.I * (θ : ℂ)) * Complex.exp (-(Complex.I * (θ : ℂ))))
            * (((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)) := by ring
      _ = ((1 / 2 : ℝ) : ℂ) := by rw [hexp, one_mul, sqrt_two_sq]

/-- **The kernel is not determined by its diagonal.**  Two relative phases give the same visible
probability law and different kernels. -/
theorem coherentBeta_kernel_ne :
    rankOneKernel (coherentBeta 0) ≠ rankOneKernel (coherentBeta Real.pi) := by
  intro hcon
  have h01 : coherentBeta 0 0 * (starRingEnd ℂ) (coherentBeta 0 1)
      = coherentBeta Real.pi 0 * (starRingEnd ℂ) (coherentBeta Real.pi 1) :=
    congrFun (congrFun hcon 0) 1
  have hzero : Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) = 1 := by simp
  have hpi : Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)) = -1 := by
    rw [show Complex.I * ((Real.pi : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  have hL : coherentBeta 0 0 * (starRingEnd ℂ) (coherentBeta 0 1) = ((1 / 2 : ℝ) : ℂ) := by
    show ((1 / Real.sqrt 2 : ℝ) : ℂ)
      * (starRingEnd ℂ) (Complex.exp (Complex.I * ((0 : ℝ) : ℂ))
        * ((1 / Real.sqrt 2 : ℝ) : ℂ)) = _
    rw [hzero, one_mul, Complex.conj_ofReal, sqrt_two_sq]
  have hR : coherentBeta Real.pi 0 * (starRingEnd ℂ) (coherentBeta Real.pi 1)
      = -((1 / 2 : ℝ) : ℂ) := by
    show ((1 / Real.sqrt 2 : ℝ) : ℂ)
      * (starRingEnd ℂ) (Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ))
        * ((1 / Real.sqrt 2 : ℝ) : ℂ)) = _
    rw [hpi, map_mul, map_neg, map_one, Complex.conj_ofReal, neg_one_mul, mul_neg, sqrt_two_sq]
  rw [hL, hR] at h01
  have hsum : ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) = 0 := by linear_combination h01
  rw [← two_mul] at hsum
  rcases mul_eq_zero.mp hsum with h | h
  · exact absurd h (by norm_num)
  · exact absurd h (by simp)

end CoherenceHidden

/-! ## §4 — the purification gauge -/

section PurificationGauge

open scoped MatrixOrder

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- **Equation (7).**  Every positive semidefinite kernel is a Gram matrix. -/
theorem exists_gram_factorization {K : Matrix B B ℂ} (hK : K.PosSemidef) :
    ∃ V : Matrix B B ℂ, K = V * Vᴴ := by
  refine ⟨CFC.sqrt K, ?_⟩
  have hpsd : (CFC.sqrt K).PosSemidef := (CFC.sqrt_nonneg K).posSemidef
  rw [hpsd.isHermitian, ← sq, CFC.sq_sqrt K]

omit [DecidableEq B] in
/-- Two Gram factorizations of the same kernel give coefficient maps of equal length. -/
theorem gram_dotProduct_eq {r : ℕ} (V W : Matrix B (Fin r) ℂ) (h : V * Vᴴ = W * Wᴴ)
    (x : B → ℂ) :
    star (Vᴴ.mulVec x) ⬝ᵥ (Vᴴ.mulVec x) = star (Wᴴ.mulVec x) ⬝ᵥ (Wᴴ.mulVec x) := by
  have key : ∀ M : Matrix B (Fin r) ℂ,
      star (Mᴴ.mulVec x) ⬝ᵥ (Mᴴ.mulVec x) = star x ⬝ᵥ ((M * Mᴴ).mulVec x) := by
    intro M
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec]
  rw [key V, key W, h]

/-- **Equation (8), the purification gauge.**  Two surjective coefficient maps of equal length
differ by a linear equivalence that preserves length; the hidden realizations of a kernel therefore
form one gauge orbit. -/
theorem ker_eq_of_norm_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f g : E →ₗ[ℂ] F)
    (hnorm : ∀ x, ‖f x‖ = ‖g x‖) : LinearMap.ker f = LinearMap.ker g := by
  ext x
  constructor
  · intro hx
    have hz : ‖g x‖ = 0 := by
      rw [← hnorm x, LinearMap.mem_ker.mp hx, norm_zero]
    exact LinearMap.mem_ker.mpr (norm_eq_zero.mp hz)
  · intro hx
    have hz : ‖f x‖ = 0 := by
      rw [hnorm x, LinearMap.mem_ker.mp hx, norm_zero]
    exact LinearMap.mem_ker.mpr (norm_eq_zero.mp hz)

noncomputable def gaugeEquiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f g : E →ₗ[ℂ] F)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hnorm : ∀ x, ‖f x‖ = ‖g x‖) : F ≃ₗ[ℂ] F :=
  ((f.quotKerEquivOfSurjective hf).symm.trans
    (Submodule.quotEquivOfEq _ _ (ker_eq_of_norm_eq f g hnorm))).trans
    (g.quotKerEquivOfSurjective hg)

theorem gaugeEquiv_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f g : E →ₗ[ℂ] F)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hnorm : ∀ x, ‖f x‖ = ‖g x‖) (x : E) :
    gaugeEquiv f g hf hg hnorm (f x) = g x := by
  show (g.quotKerEquivOfSurjective hg)
    ((Submodule.quotEquivOfEq _ _ (ker_eq_of_norm_eq f g hnorm))
      ((f.quotKerEquivOfSurjective hf).symm (f x))) = g x
  have h1 : (f.quotKerEquivOfSurjective hf).symm (f x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [h1]
  rfl

theorem gaugeEquiv_norm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f g : E →ₗ[ℂ] F)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hnorm : ∀ x, ‖f x‖ = ‖g x‖) (y : F) :
    ‖gaugeEquiv f g hf hg hnorm y‖ = ‖y‖ := by
  obtain ⟨x, rfl⟩ := hf y
  rw [gaugeEquiv_apply, hnorm]

end PurificationGauge

end GaloisForLFunctions.HTGeometry
