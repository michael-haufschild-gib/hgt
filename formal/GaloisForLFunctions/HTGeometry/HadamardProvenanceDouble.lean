import GaloisForLFunctions.HTGeometry.ContinuumFormationDefect

/-!
# The minimal Hadamard provenance double

On the Burnol carrier `H_B` both the Euler synthesis `A_E` and the continuum synthesis `A₀` have
dense range, so the atomic/continuum provenance sign cannot descend to one bounded observer, while
the Hadamard double `B(a, b) = (A_E a + A₀ b, A_E a - A₀ b)` transports it exactly.

* **Theorem MHPD-A (MHPD.1).**  `A_E` has dense range: already the prime-two depth columns
  `f_{(k+1) log 2}` are total, by Laplace uniqueness at the lattice `t ∈ ℕ log 2`.
* **Theorem MHPD-B (MHPD.2).**  No bounded `F : H_B → H_B` has `F A_E = A_E` and `F A₀ = -A₀`.
* **Theorem MHPD-C (MHPD.3)–(MHPD.7).**  `B` is Hilbert–Schmidt with dense range, `B J = S B` for the
  source grading `J(a, b) = (a, -b)` and the target swap `S`, both source outputs are recovered from
  `B`, and `‖z₊‖² + ‖z₋‖² = 2‖A_E a‖² + 2‖A₀ b‖²`.
-/

open MeasureTheory Set Filter Topology ContinuousLinearMap
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance factTwoNeTopHadamard : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-! ## Dense range from an injective adjoint -/

theorem denseRange_of_adjoint_injective {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {T : E →L[ℂ] F} (h : ∀ q, adjoint T q = 0 → q = 0) : DenseRange T := by
  have hperp : (LinearMap.range (T : E →ₗ[ℂ] F))ᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range, eq_bot_iff]
    intro q hq
    exact (Submodule.mem_bot ℂ).2 (h q hq)
  have hclos := Submodule.orthogonal_orthogonal_eq_closure (LinearMap.range (T : E →ₗ[ℂ] F))
  rw [hperp, Submodule.bot_orthogonal_eq_top] at hclos
  have hd := (Submodule.dense_iff_topologicalClosure_eq_top).2 hclos.symm
  simpa [DenseRange, LinearMap.coe_range] using hd

/-- If `f_s · q` vanishes almost everywhere on `(0, ∞)`, then `q = 0`. -/
theorem eq_zero_of_burnolRadial_mul_ae_eq_zero {s : ℝ} (q : BurnolCarrier)
    (h : (fun r => ((burnolRadial s r : ℝ) : ℂ) * q r) =ᵐ[volume.restrict (Ioi 0)] 0) : q = 0 := by
  refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
  change (q : ℝ → ℂ) =ᵐ[volume.restrict (Ici 0)] 0
  rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
  filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with r hr hpos
  have hne : ((burnolRadial s r : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, burnolRadial]
    exact mul_ne_zero (ne_of_gt hpos) (Real.exp_pos _).ne'
  exact (mul_eq_zero.1 hr).resolve_left hne

theorem withLp_ext_fst_snd {α β : Type*} {x y : WithLp 2 (α × β)} (h1 : x.fst = y.fst)
    (h2 : x.snd = y.snd) : x = y :=
  WithLp.ofLp_injective 2 (Prod.ext h1 h2)

/-! ## Theorem MHPD-A -/

/-- The prime-two depth labels `2^{k+1}`. -/
def twoPowLabel (k : ℕ) : AtomLabel :=
  ⟨2 ^ (k + 1), by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)⟩

theorem vonMangoldt_twoPowLabel_pos (k : ℕ) :
    0 < ArithmeticFunction.vonMangoldt ((twoPowLabel k : AtomLabel) : ℕ) := by
  change 0 < ArithmeticFunction.vonMangoldt (2 ^ (k + 1))
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact Real.log_pos (by norm_num)

theorem log_twoPowLabel (k : ℕ) :
    Real.log (((twoPowLabel k : AtomLabel) : ℕ) : ℝ) = ((k : ℝ) + 1) * Real.log 2 := by
  change Real.log (((2 ^ (k + 1) : ℕ) : ℝ)) = _
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  ring

variable {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
include hx hc

/-- **Theorem MHPD-A (MHPD.1).**  The Euler synthesis has dense range: a vector orthogonal to the
prime-two columns `f_{(k+1) log 2}` has `f_{log 2} q` with vanishing Laplace transform on `ℕ log 2`. -/
theorem denseRange_atomicSynthesis : DenseRange (atomicSynthesis hx.le hc.le) := by
  refine denseRange_of_adjoint_injective fun q hq => ?_
  have hn : ∀ n : AtomLabel, ⟪eulerColumn x c n, q⟫_ℂ = 0 := by
    intro n
    rw [← atomicSynthesis_labelBasisVec hx.le hc.le n, ← adjoint_inner_right, hq, inner_zero_right]
  set a := Real.log 2 with hadef
  have ha : 0 < a := Real.log_pos one_lt_two
  have hpair : ∀ k : ℕ, radialPairing q (((k : ℝ) + 1) * a) = 0 := by
    intro k
    have h := hn (twoPowLabel k)
    rw [eulerColumn, inner_smul_left, inner_radialLp, Complex.conj_ofReal] at h
    have hne : (atomicCoefficient x c (twoPowLabel k) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (atomicCoefficient_pos hc (vonMangoldt_twoPowLabel_pos k)).ne'
    have h1 := (mul_eq_zero.1 h).resolve_left hne
    rwa [log_twoPowLabel] at h1
  set g : ℝ → ℂ := fun r => ((burnolRadial a r : ℝ) : ℂ) * q r with hgdef
  have hg : IntegrableOn g (Ioi 0) := by
    have h1 := (memLp_burnolRadial ha).integrable_mul (Lp.memLp q)
    exact (show IntegrableOn g (Ici 0) volume from h1).mono_set Ioi_subset_Ici_self
  have hshift : ∀ k : ℕ, radialPairing q (((k : ℝ) + 1) * a) =
      ∫ r in Ioi 0, g r * (Real.exp (-((k : ℝ) * a) * r) : ℂ) := by
    intro k
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [hgdef, burnolRadial]
    rw [show -(((k : ℝ) + 1) * a * r) = -(a * r) + -((k : ℝ) * a) * r by ring, Real.exp_add]
    push_cast
    ring
  have hg0 := ae_eq_zero_of_laplace_nat_eq_zero hg ha fun k => by rw [← hshift]; exact hpair k
  exact eq_zero_of_burnolRadial_mul_ae_eq_zero q hg0

/-! ## Theorem MHPD-B -/

omit hx hc in
theorem radialLp_ne_zero {s : ℝ} (hs : 0 < s) : radialLp hs ≠ 0 := by
  intro h0
  have h1 := radialLp_coeFn hs
  rw [h0] at h1
  have h2 := ae_restrict_of_ae_restrict_of_subset Ioi_subset_Ici_self
    ((Lp.coeFn_zero ℂ 2 halfLineMeasure).symm.trans h1)
  have h3 : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), False := by
    filter_upwards [h2, ae_restrict_mem measurableSet_Ioi] with r hr hpos
    have : ((burnolRadial s r : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, burnolRadial]
      exact mul_ne_zero (ne_of_gt hpos) (Real.exp_pos _).ne'
    exact this hr.symm
  have hne : volume.restrict (Ioi (0 : ℝ)) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioi]
    exact ENNReal.top_ne_zero
  haveI := ae_neBot.2 hne
  exact h3.exists.elim fun _ h => h

/-- **Theorem MHPD-B (MHPD.2).**  The atomic/continuum sign is not a bounded observable of the
completed carrier: `F A_E = A_E` forces `F = I` on the dense range of `A_E`, and then `A₀ = -A₀`
forces `A₀ = 0`, contradicting injectivity. -/
theorem not_exists_provenanceDescent :
    ¬ ∃ F : BurnolCarrier →L[ℂ] BurnolCarrier,
      F ∘L atomicSynthesis hx.le hc.le = atomicSynthesis hx.le hc.le ∧
        F ∘L continuumSynthesis hx hc = -continuumSynthesis hx hc := by
  rintro ⟨F, h1, h2⟩
  have hF : F = ContinuousLinearMap.id ℂ BurnolCarrier := by
    have := (denseRange_atomicSynthesis hx hc).equalizer F.continuous continuous_id
      (funext fun a => congrFun (congrArg DFunLike.coe h1) a)
    exact ContinuousLinearMap.ext (congrFun this)
  rw [hF, id_comp] at h2
  have h0 : continuumSynthesis hx hc (radialLp one_pos) = 0 := by
    have hv := congrFun (congrArg DFunLike.coe h2) (radialLp one_pos)
    simp only [neg_apply] at hv
    have h3 : (2 : ℂ) • continuumSynthesis hx hc (radialLp one_pos) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hv]
      exact add_neg_cancel _
    exact (smul_eq_zero.1 h3).resolve_left two_ne_zero
  exact radialLp_ne_zero one_pos
    (continuumSynthesis_injective hx hc (h0.trans (map_zero _).symm))

/-! ## Theorem MHPD-C: the Hadamard double -/

/-- **(MHPD.3)** The Hadamard formation synthesis `B(a, b) = (A_E a + A₀ b, A_E a - A₀ b)`. -/
def hadamardSynthesis :
    WithLp 2 (Lp ℂ 2 (Measure.count : Measure AtomLabel) × BurnolCarrier) →L[ℂ]
      WithLp 2 (BurnolCarrier × BurnolCarrier) :=
  columnAnalysis (adjoint (rowSynthesis (atomicSynthesis hx.le hc.le) (continuumSynthesis hx hc)))
    (adjoint (rowSynthesis (atomicSynthesis hx.le hc.le) (-continuumSynthesis hx hc)))

theorem hadamardSynthesis_apply
    (v : WithLp 2 (Lp ℂ 2 (Measure.count : Measure AtomLabel) × BurnolCarrier)) :
    hadamardSynthesis hx hc v = WithLp.toLp 2
      (atomicSynthesis hx.le hc.le v.fst + continuumSynthesis hx hc v.snd,
        atomicSynthesis hx.le hc.le v.fst - continuumSynthesis hx hc v.snd) := by
  rw [hadamardSynthesis, columnAnalysis_apply, adjoint_adjoint, adjoint_adjoint, rowSynthesis_apply,
    rowSynthesis_apply, neg_apply, ← sub_eq_add_neg]

omit hx hc in
/-- **(MHPD.4)** The target swap `S(z₊, z₋) = (z₋, z₊)`. -/
def hadamardSwap : WithLp 2 (BurnolCarrier × BurnolCarrier) →L[ℂ]
    WithLp 2 (BurnolCarrier × BurnolCarrier) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ BurnolCarrier BurnolCarrier).symm :
      BurnolCarrier × BurnolCarrier →L[ℂ] WithLp 2 (BurnolCarrier × BurnolCarrier)) ∘L
    ((ContinuousLinearMap.snd ℂ BurnolCarrier BurnolCarrier).prod
      (ContinuousLinearMap.fst ℂ BurnolCarrier BurnolCarrier)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ BurnolCarrier BurnolCarrier :
      WithLp 2 (BurnolCarrier × BurnolCarrier) →L[ℂ] BurnolCarrier × BurnolCarrier)

omit hx hc in
theorem hadamardSwap_apply (z : WithLp 2 (BurnolCarrier × BurnolCarrier)) :
    hadamardSwap z = WithLp.toLp 2 (z.snd, z.fst) := rfl

/-- **Theorem MHPD-C (MHPD.5)** Exact grading transport `B J = S B`, `J = diag(1, -1)`. -/
theorem hadamardSynthesis_grading :
    hadamardSynthesis hx hc ∘L gradingOp 1 (-1) = hadamardSwap ∘L hadamardSynthesis hx hc := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hadamardSwap_apply,
    hadamardSynthesis_apply, hadamardSynthesis_apply]
  simp only [gradingOp, blockDiag, ContinuousLinearMap.comp_apply]
  simp [sub_eq_add_neg]

/-- **Theorem MHPD-C (MHPD.6)** Both source outputs are recovered from `z = B(a, b)`:
`A_E a = (z₊ + z₋)/2`, `A₀ b = (z₊ - z₋)/2`. -/
theorem hadamardSynthesis_recovery
    (v : WithLp 2 (Lp ℂ 2 (Measure.count : Measure AtomLabel) × BurnolCarrier)) :
    atomicSynthesis hx.le hc.le v.fst =
        (1 / 2 : ℂ) • ((hadamardSynthesis hx hc v).fst + (hadamardSynthesis hx hc v).snd) ∧
      continuumSynthesis hx hc v.snd =
        (1 / 2 : ℂ) • ((hadamardSynthesis hx hc v).fst - (hadamardSynthesis hx hc v).snd) := by
  rw [hadamardSynthesis_apply]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  constructor
  · rw [show atomicSynthesis hx.le hc.le v.fst + continuumSynthesis hx hc v.snd +
        (atomicSynthesis hx.le hc.le v.fst - continuumSynthesis hx hc v.snd) =
        (2 : ℂ) • atomicSynthesis hx.le hc.le v.fst by rw [two_smul]; abel, smul_smul]
    norm_num
  · rw [show atomicSynthesis hx.le hc.le v.fst + continuumSynthesis hx hc v.snd -
        (atomicSynthesis hx.le hc.le v.fst - continuumSynthesis hx hc v.snd) =
        (2 : ℂ) • continuumSynthesis hx hc v.snd by rw [two_smul]; abel, smul_smul]
    norm_num

/-- **Theorem MHPD-C (MHPD.7)** Energy conservation `‖z₊‖² + ‖z₋‖² = 2‖A_E a‖² + 2‖A₀ b‖²`. -/
theorem norm_hadamardSynthesis_sq
    (v : WithLp 2 (Lp ℂ 2 (Measure.count : Measure AtomLabel) × BurnolCarrier)) :
    ‖hadamardSynthesis hx hc v‖ ^ 2 =
      2 * ‖atomicSynthesis hx.le hc.le v.fst‖ ^ 2 + 2 * ‖continuumSynthesis hx hc v.snd‖ ^ 2 := by
  rw [hadamardSynthesis_apply, WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  have h := parallelogram_law_with_norm ℂ (atomicSynthesis hx.le hc.le v.fst)
    (continuumSynthesis hx hc v.snd)
  nlinarith [h]

/-- **Theorem MHPD-C** `B` is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_hadamardSynthesis : IsHilbertSchmidt (hadamardSynthesis hx hc) := by
  have hE := isHilbertSchmidt_atomicSynthesis hx.le hc.le
  have h0 := isHilbertSchmidt_continuumSynthesis hx hc
  have h0' : IsHilbertSchmidt (-continuumSynthesis hx hc) := by
    rw [← neg_one_smul ℂ (continuumSynthesis hx hc)]
    exact h0.smul (-1)
  exact isHilbertSchmidt_columnAnalysis (isHilbertSchmidt_rowSynthesis hE h0).adjoint
    (isHilbertSchmidt_rowSynthesis hE h0').adjoint

/-- **Theorem MHPD-C** `B` has dense range: its range contains the diagonal `(A_E a, A_E a)` and the
antidiagonal `(A₀ b, -A₀ b)`, whose closures are the full diagonal and antidiagonal. -/
theorem denseRange_hadamardSynthesis : DenseRange (hadamardSynthesis hx hc) := by
  set Bsub := LinearMap.range (hadamardSynthesis hx hc :
    WithLp 2 (Lp ℂ 2 (Measure.count : Measure AtomLabel) × BurnolCarrier) →ₗ[ℂ]
      WithLp 2 (BurnolCarrier × BurnolCarrier))
  have hdiag : ∀ (P : BurnolCarrier →L[ℂ] WithLp 2 (BurnolCarrier × BurnolCarrier))
      {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] (A : G →L[ℂ] BurnolCarrier),
      DenseRange A → (∀ g, ∃ v, hadamardSynthesis hx hc v = P (A g)) →
        ∀ w, P w ∈ Bsub.topologicalClosure := by
    intro P G _ _ A hA hP w
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    have hsub : P '' Set.range A ⊆ (Bsub : Set _) := by
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      obtain ⟨v, hv⟩ := hP g
      exact ⟨v, hv⟩
    have hw : P w ∈ P '' closure (Set.range A) := ⟨w, by rw [hA.closure_range]; trivial, rfl⟩
    exact closure_mono hsub (image_closure_subset_closure_image P.continuous hw)
  set Δ : BurnolCarrier →L[ℂ] WithLp 2 (BurnolCarrier × BurnolCarrier) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℂ BurnolCarrier BurnolCarrier).symm :
      BurnolCarrier × BurnolCarrier →L[ℂ] WithLp 2 (BurnolCarrier × BurnolCarrier)) ∘L
      ((ContinuousLinearMap.id ℂ BurnolCarrier).prod (ContinuousLinearMap.id ℂ BurnolCarrier))
  set Δ' : BurnolCarrier →L[ℂ] WithLp 2 (BurnolCarrier × BurnolCarrier) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℂ BurnolCarrier BurnolCarrier).symm :
      BurnolCarrier × BurnolCarrier →L[ℂ] WithLp 2 (BurnolCarrier × BurnolCarrier)) ∘L
      ((ContinuousLinearMap.id ℂ BurnolCarrier).prod (-ContinuousLinearMap.id ℂ BurnolCarrier))
  have h1 := hdiag Δ (atomicSynthesis hx.le hc.le) (denseRange_atomicSynthesis hx hc) fun a =>
    ⟨WithLp.toLp 2 (a, 0), by rw [hadamardSynthesis_apply]; simp [Δ]⟩
  have h2 := hdiag Δ' (continuumSynthesis hx hc) (denseRange_continuumSynthesis hx hc) fun b =>
    ⟨WithLp.toLp 2 (0, b), by rw [hadamardSynthesis_apply]; simp [Δ', sub_eq_add_neg]⟩
  intro z
  obtain ⟨p, q⟩ := z
  have hΔ : ∀ w, Δ w = WithLp.toLp 2 (w, w) := fun w => rfl
  have hΔ' : ∀ w, Δ' w = WithLp.toLp 2 (w, -w) := fun w => rfl
  have hz : WithLp.toLp 2 (p, q) = Δ ((1 / 2 : ℂ) • (p + q)) + Δ' ((1 / 2 : ℂ) • (p - q)) := by
    rw [hΔ, hΔ']
    refine withLp_ext_fst_snd ?_ ?_
    · simp only [WithLp.add_fst, WithLp.toLp_fst]
      module
    · simp only [WithLp.add_snd, WithLp.toLp_snd]
      module
  have hmem := Bsub.topologicalClosure.add_mem (h1 ((1 / 2 : ℂ) • (p + q)))
    (h2 ((1 / 2 : ℂ) • (p - q)))
  rw [← hz, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hmem
  simpa [Bsub, LinearMap.coe_range] using hmem

/-- **Minimality.**  One completed channel cannot carry the provenance sign (MHPD-B), while the
Hadamard pair transports it exactly (MHPD-C). -/
theorem hadamard_minimal :
    (¬ ∃ F : BurnolCarrier →L[ℂ] BurnolCarrier,
      F ∘L atomicSynthesis hx.le hc.le = atomicSynthesis hx.le hc.le ∧
        F ∘L continuumSynthesis hx hc = -continuumSynthesis hx hc) ∧
      hadamardSynthesis hx hc ∘L gradingOp 1 (-1) = hadamardSwap ∘L hadamardSynthesis hx hc :=
  ⟨not_exists_provenanceDescent hx hc, hadamardSynthesis_grading hx hc⟩

end GaloisForLFunctions.HTGeometry
