import GaloisForLFunctions.RHTower.BurnolCoPoissonQuotientOrder
import GaloisForLFunctions.RHTower.BurnolSoninDilationMellin

/-!
# The co-Poisson quotient kernels form a two-coordinate projective Sonine section

Along the geometric aperture sequence `a_j = a r^{-j}` with `r ≥ 1`, the normalized dilation and its
adjoint both carry the extended Sonine space at aperture `a_j` into the space at `a_{j+1}`.
Composing either with the orthogonal projection `E_j` onto the co-Poisson quotient at level `j`
gives two bonding maps

`T_j^+ = E_j U_r^*`,  `T_j^- = E_j U_r`,

each a contraction.  At a point annihilating every closed co-Poisson source the quotient evaluation
vector is the ambient completed-Mellin Riesz vector, and the exact Mellin dilation character
`λ = r^(w-1/2)` turns both bonding maps into scalar multiplications on it:

`T_j^+ y_{w,j+1} = conj λ • y_{w,j}`,  `T_j^- y_{w,j+1} = conj λ⁻¹ • y_{w,j}`.

Contractivity along the ladder then forces the two-sided geometric lower bound

`‖y_{w,N}‖ ≥ max(|λ|^N, |λ|^{-N}) ‖y_{w,0}‖`,

and the quadrant coordinates `X_{p,q} = conj λ^{q-p} • y_{w,p+q}` obey both projective bonding laws,
commuting squares, and the escape bound `‖X_{p,q}‖ ≥ max(|λ|^{2q}, |λ|^{-2p}) ‖X_{0,0}‖`, whose
exponent is the horizontal displacement `Re w - 1/2` of the character.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-! ## The aperture ladder -/

/-- Geometric aperture sequence `a_j = a r^{-j}`. -/
def soninAperture (a r : ℝ) (j : ℕ) : ℝ := a / r ^ j

theorem soninAperture_pos {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (j : ℕ) :
    0 < soninAperture a r j :=
  div_pos ha (pow_pos hr j)

@[simp] theorem soninAperture_zero (a r : ℝ) : soninAperture a r 0 = a := by
  simp [soninAperture]

theorem soninAperture_succ {a r : ℝ} (hr : 0 < r) (j : ℕ) :
    soninAperture a r (j + 1) = r⁻¹ * soninAperture a r j := by
  unfold soninAperture
  rw [pow_succ]
  field_simp

/-- The exact normalized Mellin character of one ladder step. -/
def soninLadderCharacter (w : ℂ) (r : ℝ) : ℂ := (r : ℂ) ^ (w - 1 / 2)

theorem soninLadderCharacter_ne_zero (hr : 0 < r) (w : ℂ) : soninLadderCharacter w r ≠ 0 := by
  have hrne : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
  simp [soninLadderCharacter, hrne]

/-- The modulus of the ladder character is the horizontal displacement of `w`. -/
theorem norm_soninLadderCharacter (hr : 0 < r) (w : ℂ) :
    ‖soninLadderCharacter w r‖ = r ^ (w.re - 1 / 2) := by
  rw [soninLadderCharacter, Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

theorem norm_soninLadderCharacter_pos (hr : 0 < r) (w : ℂ) :
    0 < ‖soninLadderCharacter w r‖ :=
  norm_pos_iff.mpr (soninLadderCharacter_ne_zero hr w)

/-! ## The two quotient bonding maps -/

/-- The forward quotient bonding map `T_j^+ = E_j U_r^*`, where `U_r^*` is the normalized dilation
by `r⁻¹`. -/
def coPoissonQuotientForward (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (j : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  (burnolCoPoissonQuotientProjection (soninAperture a r j)
      (soninAperture_pos ha hr j)).comp
    (evenDilationCLM r⁻¹ (inv_pos.mpr hr))

/-- The inverse quotient bonding map `T_j^- = E_j U_r`. -/
def coPoissonQuotientInverse (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (j : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  (burnolCoPoissonQuotientProjection (soninAperture a r j)
      (soninAperture_pos ha hr j)).comp
    (evenDilationCLM r hr)

theorem coPoissonQuotientForward_apply_mem (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (j : ℕ)
    (f : evenSubspace) :
    coPoissonQuotientForward a r ha hr j f ∈
      burnolCoPoissonQuotientSpace (soninAperture a r j) :=
  burnolCoPoissonQuotientProjection_apply_mem _ (soninAperture_pos ha hr j) _

theorem coPoissonQuotientInverse_apply_mem (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (j : ℕ)
    (f : evenSubspace) :
    coPoissonQuotientInverse a r ha hr j f ∈
      burnolCoPoissonQuotientSpace (soninAperture a r j) :=
  burnolCoPoissonQuotientProjection_apply_mem _ (soninAperture_pos ha hr j) _

/-- Both bonding maps are contractions: an orthogonal projection composed with a unitary. -/
theorem norm_coPoissonQuotientForward_apply_le (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (j : ℕ)
    (f : evenSubspace) :
    ‖coPoissonQuotientForward a r ha hr j f‖ ≤ ‖f‖ := by
  letI : CompleteSpace (burnolCoPoissonQuotientSpace (soninAperture a r j)) :=
    (isClosed_burnolCoPoissonQuotientSpace (soninAperture_pos ha hr j)).completeSpace_coe
  have hproj := (burnolCoPoissonQuotientSpace (soninAperture a r j)).norm_starProjection_apply_le
    (evenDilationCLM r⁻¹ (inv_pos.mpr hr) f)
  have hdil := norm_evenDilationCLM_apply r⁻¹ (inv_pos.mpr hr) f
  calc ‖coPoissonQuotientForward a r ha hr j f‖ ≤
      ‖evenDilationCLM r⁻¹ (inv_pos.mpr hr) f‖ := hproj
    _ = ‖f‖ := hdil

theorem norm_coPoissonQuotientInverse_apply_le (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (j : ℕ)
    (f : evenSubspace) :
    ‖coPoissonQuotientInverse a r ha hr j f‖ ≤ ‖f‖ := by
  letI : CompleteSpace (burnolCoPoissonQuotientSpace (soninAperture a r j)) :=
    (isClosed_burnolCoPoissonQuotientSpace (soninAperture_pos ha hr j)).completeSpace_coe
  have hproj := (burnolCoPoissonQuotientSpace (soninAperture a r j)).norm_starProjection_apply_le
    (evenDilationCLM r hr f)
  have hdil := norm_evenDilationCLM_apply r hr f
  calc ‖coPoissonQuotientInverse a r ha hr j f‖ ≤ ‖evenDilationCLM r hr f‖ := hproj
    _ = ‖f‖ := hdil

/-! ## The exact bonding characters at a co-Poisson annihilator point -/

/-- Two vectors of a subspace agreeing against every test vector of that subspace are equal. -/
theorem eq_of_forall_inner_eq_of_mem {K : Submodule ℂ evenSubspace} {x y : evenSubspace}
    (hx : x ∈ K) (hy : y ∈ K) (h : ∀ f ∈ K, ⟪x, f⟫_ℂ = ⟪y, f⟫_ℂ) : x = y := by
  have hxy : x - y ∈ K := K.sub_mem hx hy
  have hzero : ⟪x - y, x - y⟫_ℂ = 0 := by
    rw [inner_sub_left, h _ hxy, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

theorem burnolCoPoissonQuotientProjection_eq_self {b : ℝ} (hb : 0 < b) {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonQuotientSpace b) :
    burnolCoPoissonQuotientProjection b hb f = f := by
  letI : CompleteSpace (burnolCoPoissonQuotientSpace b) :=
    (isClosed_burnolCoPoissonQuotientSpace hb).completeSpace_coe
  exact Submodule.starProjection_eq_self_iff.mpr hf

/-- The normalized dilation moves the extended Sonine space one step down the aperture ladder. -/
theorem evenDilation_mem_soninExtendedSpace_succ {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hr1 : 1 ≤ r)
    (j : ℕ) {f : evenSubspace} (hf : f ∈ soninExtendedSpace (soninAperture a r j)) :
    evenDilationCLM r hr f ∈ soninExtendedSpace (soninAperture a r (j + 1)) := by
  rw [soninAperture_succ hr]
  exact evenDilation_mem_soninExtendedSpace_inv_mul (soninAperture_pos ha hr j) hr1 hf

/-- The adjoint dilation moves the extended Sonine space one step down the aperture ladder too. -/
theorem evenInverseDilation_mem_soninExtendedSpace_succ {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hr1 : 1 ≤ r) (j : ℕ) {f : evenSubspace}
    (hf : f ∈ soninExtendedSpace (soninAperture a r j)) :
    evenDilationCLM r⁻¹ (inv_pos.mpr hr) f ∈ soninExtendedSpace (soninAperture a r (j + 1)) := by
  rw [soninAperture_succ hr]
  exact evenInverseDilation_mem_soninExtendedSpace_inv_mul (soninAperture_pos ha hr j) hr1 hf

/-- Ambient form of the reproducing identity for the completed Mellin evaluation vector. -/
theorem inner_burnolExtendedSoninEvaluationVector_coe
    (w : ℂ) (b : ℝ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b)
    {g : evenSubspace} (hg : g ∈ soninExtendedSpace b) :
    ⟪(burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace), g⟫_ℂ =
      soninMellinEvaluation w ((g : SoninL2) : ℝ → ℂ) := by
  have h := inner_burnolExtendedSoninEvaluationVector w b hlo hhi hb ⟨g, hg⟩
  rw [Submodule.coe_inner] at h
  exact h

/-- Ambient form of the reproducing identity on the co-Poisson quotient. -/
theorem inner_burnolCoPoissonQuotientEvaluationVector_coe
    (w : ℂ) (b : ℝ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b)
    {g : evenSubspace} (hg : g ∈ burnolCoPoissonQuotientSpace b) :
    ⟪(burnolCoPoissonQuotientEvaluationVector w b hlo hhi hb : evenSubspace), g⟫_ℂ =
      soninMellinEvaluation w ((g : SoninL2) : ℝ → ℂ) := by
  have h := inner_burnolCoPoissonQuotientEvaluationVector w b hlo hhi hb ⟨g, hg⟩
  rw [Submodule.coe_inner] at h
  exact h

/-! ## The ladder of kernels -/

variable {w : ℂ} {a r : ℝ}

/-- The completed Mellin evaluation vector at level `j` of the aperture ladder. -/
def soninLadderKernel (w : ℂ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (j : ℕ) : evenSubspace :=
  (burnolExtendedSoninEvaluationVector w (soninAperture a r j) hlo hhi
    (soninAperture_pos ha hr j) : evenSubspace)

theorem soninLadderKernel_mem (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (ha : 0 < a) (hr : 0 < r) (j : ℕ) :
    soninLadderKernel w hlo hhi a r ha hr j ∈ soninExtendedSpace (soninAperture a r j) :=
  (burnolExtendedSoninEvaluationVector w (soninAperture a r j) hlo hhi
    (soninAperture_pos ha hr j)).property

/-- The co-Poisson quotient kernel `y_{w,j} = E_j k_{w,j}` at level `j`. -/
def coPoissonLadderKernel (w : ℂ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (j : ℕ) : evenSubspace :=
  (burnolCoPoissonQuotientEvaluationVector w (soninAperture a r j) hlo hhi
    (soninAperture_pos ha hr j) : evenSubspace)

theorem coPoissonLadderKernel_mem (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (ha : 0 < a) (hr : 0 < r) (j : ℕ) :
    coPoissonLadderKernel w hlo hhi a r ha hr j ∈
      burnolCoPoissonQuotientSpace (soninAperture a r j) :=
  (burnolCoPoissonQuotientEvaluationVector w (soninAperture a r j) hlo hhi
    (soninAperture_pos ha hr j)).property

/-- A regular point annihilating every closed co-Poisson source at every aperture of the ladder. -/
def CoPoissonLadderAnnihilator (w : ℂ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r) : Prop :=
  ∀ j : ℕ, BurnolCoPoissonAnnihilatorPoint w (soninAperture a r j) hlo hhi
    (soninAperture_pos ha hr j)

/-- On the annihilator locus the quotient kernel is the ambient completed-Mellin kernel. -/
theorem coPoissonLadderKernel_eq_soninLadderKernel {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (j : ℕ) :
    coPoissonLadderKernel w hlo hhi a r ha hr j = soninLadderKernel w hlo hhi a r ha hr j :=
  coe_burnolCoPoissonQuotientEvaluationVector_eq_of_annihilator hlo hhi
    (soninAperture_pos ha hr j) (hann j)

/-- Testing the co-Poisson projection against a vector of its own range removes it. -/
theorem inner_burnolCoPoissonQuotientProjection_left {b : ℝ} (hb : 0 < b)
    (x : evenSubspace) {f : evenSubspace} (hf : f ∈ burnolCoPoissonQuotientSpace b) :
    ⟪burnolCoPoissonQuotientProjection b hb x, f⟫_ℂ = ⟪x, f⟫_ℂ := by
  letI : CompleteSpace (burnolCoPoissonQuotientSpace b) :=
    (isClosed_burnolCoPoissonQuotientSpace hb).completeSpace_coe
  have hzero : ⟪x - (burnolCoPoissonQuotientSpace b).starProjection x, f⟫_ℂ = 0 :=
    Submodule.starProjection_inner_eq_zero x f hf
  rw [inner_sub_left, sub_eq_zero] at hzero
  exact hzero.symm

theorem inner_smul_left_evenSubspace (c : ℂ) (x f : evenSubspace) :
    ⟪c • x, f⟫_ℂ = (starRingEnd ℂ) c * ⟪x, f⟫_ℂ := by
  simp [mul_comm]

/-- **The exact forward bonding character**, without any hypothesis on `w`.  Applying
`T_j^+ = E_j U_r^*` to the *ambient* completed-Mellin kernel at level `j+1` returns the co-Poisson
quotient kernel at level `j`, scaled by the conjugate character. -/
theorem coPoissonQuotientForward_soninLadderKernel {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r) (j : ℕ) :
    coPoissonQuotientForward a r ha hr j (soninLadderKernel w hlo hhi a r ha hr (j + 1)) =
      (starRingEnd ℂ) (soninLadderCharacter w r) • coPoissonLadderKernel w hlo hhi a r ha hr j := by
  refine eq_of_forall_inner_eq_of_mem
    (K := burnolCoPoissonQuotientSpace (soninAperture a r j))
    (coPoissonQuotientForward_apply_mem a r ha hr j _)
    (Submodule.smul_mem _ _ (coPoissonLadderKernel_mem hlo hhi ha hr j)) ?_
  intro f hf
  have hfL : f ∈ soninExtendedSpace (soninAperture a r j) := hf.1
  have hdil : evenDilationCLM r hr f ∈ soninExtendedSpace (soninAperture a r (j + 1)) :=
    evenDilation_mem_soninExtendedSpace_succ ha hr hr1 j hfL
  have hadj : ContinuousLinearMap.adjoint (evenDilationCLM r hr) =
      evenDilationCLM r⁻¹ (inv_pos.mpr hr) := adjoint_evenDilationCLM r hr
  have hLHS :
      ⟪coPoissonQuotientForward a r ha hr j
          (soninLadderKernel w hlo hhi a r ha hr (j + 1)), f⟫_ℂ =
        soninLadderCharacter w r * soninMellinEvaluation w ((f : SoninL2) : ℝ → ℂ) := by
    rw [coPoissonQuotientForward, ContinuousLinearMap.comp_apply,
      inner_burnolCoPoissonQuotientProjection_left (soninAperture_pos ha hr j) _ hf, ← hadj,
      ContinuousLinearMap.adjoint_inner_left (evenDilationCLM r hr) f
        (soninLadderKernel w hlo hhi a r ha hr (j + 1)),
      soninLadderKernel,
      inner_burnolExtendedSoninEvaluationVector_coe w (soninAperture a r (j + 1)) hlo hhi
        (soninAperture_pos ha hr (j + 1)) hdil,
      soninMellinEvaluation_evenDilation w r hr f, soninLadderCharacter]
  have hRHS :
      ⟪(starRingEnd ℂ) (soninLadderCharacter w r) •
          coPoissonLadderKernel w hlo hhi a r ha hr j, f⟫_ℂ =
        soninLadderCharacter w r * soninMellinEvaluation w ((f : SoninL2) : ℝ → ℂ) := by
    rw [inner_smul_left_evenSubspace, Complex.conj_conj, coPoissonLadderKernel,
      inner_burnolCoPoissonQuotientEvaluationVector_coe w (soninAperture a r j) hlo hhi
        (soninAperture_pos ha hr j) hf]
  rw [hLHS, hRHS]

/-- **The exact inverse bonding character**, without any hypothesis on `w`. -/
theorem coPoissonQuotientInverse_soninLadderKernel {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r) (j : ℕ) :
    coPoissonQuotientInverse a r ha hr j (soninLadderKernel w hlo hhi a r ha hr (j + 1)) =
      (starRingEnd ℂ) ((soninLadderCharacter w r)⁻¹) •
        coPoissonLadderKernel w hlo hhi a r ha hr j := by
  refine eq_of_forall_inner_eq_of_mem
    (K := burnolCoPoissonQuotientSpace (soninAperture a r j))
    (coPoissonQuotientInverse_apply_mem a r ha hr j _)
    (Submodule.smul_mem _ _ (coPoissonLadderKernel_mem hlo hhi ha hr j)) ?_
  intro f hf
  have hfL : f ∈ soninExtendedSpace (soninAperture a r j) := hf.1
  have hdil : evenDilationCLM r⁻¹ (inv_pos.mpr hr) f ∈
      soninExtendedSpace (soninAperture a r (j + 1)) :=
    evenInverseDilation_mem_soninExtendedSpace_succ ha hr hr1 j hfL
  have hadj : ContinuousLinearMap.adjoint (evenDilationCLM r⁻¹ (inv_pos.mpr hr)) =
      evenDilationCLM r hr := by
    rw [adjoint_evenDilationCLM r⁻¹ (inv_pos.mpr hr)]
    congr 1
    exact inv_inv r
  have hchar : ((r⁻¹ : ℝ) : ℂ) ^ (w - 1 / 2) = (soninLadderCharacter w r)⁻¹ := by
    rw [soninLadderCharacter]
    rw [Complex.ofReal_inv]
    refine Complex.inv_cpow (r : ℂ) (w - 1 / 2) ?_
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact (Real.pi_ne_zero).symm
  have hLHS :
      ⟪coPoissonQuotientInverse a r ha hr j
          (soninLadderKernel w hlo hhi a r ha hr (j + 1)), f⟫_ℂ =
        (soninLadderCharacter w r)⁻¹ * soninMellinEvaluation w ((f : SoninL2) : ℝ → ℂ) := by
    rw [coPoissonQuotientInverse, ContinuousLinearMap.comp_apply,
      inner_burnolCoPoissonQuotientProjection_left (soninAperture_pos ha hr j) _ hf, ← hadj,
      ContinuousLinearMap.adjoint_inner_left (evenDilationCLM r⁻¹ (inv_pos.mpr hr)) f
        (soninLadderKernel w hlo hhi a r ha hr (j + 1)),
      soninLadderKernel,
      inner_burnolExtendedSoninEvaluationVector_coe w (soninAperture a r (j + 1)) hlo hhi
        (soninAperture_pos ha hr (j + 1)) hdil,
      soninMellinEvaluation_evenDilation w r⁻¹ (inv_pos.mpr hr) f, hchar]
  have hRHS :
      ⟪(starRingEnd ℂ) ((soninLadderCharacter w r)⁻¹) •
          coPoissonLadderKernel w hlo hhi a r ha hr j, f⟫_ℂ =
        (soninLadderCharacter w r)⁻¹ * soninMellinEvaluation w ((f : SoninL2) : ℝ → ℂ) := by
    rw [inner_smul_left_evenSubspace, Complex.conj_conj, coPoissonLadderKernel,
      inner_burnolCoPoissonQuotientEvaluationVector_coe w (soninAperture a r j) hlo hhi
        (soninAperture_pos ha hr j) hf]
  rw [hLHS, hRHS]

/-! ### The off-divisor comparison and its boundary value -/

/-- The co-Poisson source defect of the ambient completed-Mellin kernel at level `j`. -/
def coPoissonLadderDefect (w : ℂ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (j : ℕ) : evenSubspace :=
  burnolCoPoissonSourceProjection (soninAperture a r j)
    (soninLadderKernel w hlo hhi a r ha hr j)

theorem soninLadderKernel_eq_add_defect {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (j : ℕ) :
    soninLadderKernel w hlo hhi a r ha hr j =
      coPoissonLadderKernel w hlo hhi a r ha hr j +
        coPoissonLadderDefect w hlo hhi a r ha hr j := by
  rw [coPoissonLadderKernel, coPoissonLadderDefect, soninLadderKernel,
    coe_burnolCoPoissonQuotientEvaluationVector]
  abel

/-- **The exact off-divisor forward comparison.**  The forward bonding map moves the quotient
kernel by the exact character, up to the image of the co-Poisson source defect. -/
theorem coPoissonQuotientForward_ladderKernel_offDivisor {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r) (j : ℕ) :
    coPoissonQuotientForward a r ha hr j (coPoissonLadderKernel w hlo hhi a r ha hr (j + 1)) =
      (starRingEnd ℂ) (soninLadderCharacter w r) • coPoissonLadderKernel w hlo hhi a r ha hr j -
        coPoissonQuotientForward a r ha hr j
          (coPoissonLadderDefect w hlo hhi a r ha hr (j + 1)) := by
  have hsplit := soninLadderKernel_eq_add_defect (w := w) (hlo := hlo) (hhi := hhi)
    (ha := ha) (hr := hr) (j + 1)
  have hmap := coPoissonQuotientForward_soninLadderKernel (hlo := hlo) (hhi := hhi)
    (ha := ha) (hr := hr) hr1 j
  rw [hsplit, map_add] at hmap
  rw [← hmap]
  abel

/-- **The exact off-divisor inverse comparison.** -/
theorem coPoissonQuotientInverse_ladderKernel_offDivisor {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r) (j : ℕ) :
    coPoissonQuotientInverse a r ha hr j (coPoissonLadderKernel w hlo hhi a r ha hr (j + 1)) =
      (starRingEnd ℂ) ((soninLadderCharacter w r)⁻¹) •
          coPoissonLadderKernel w hlo hhi a r ha hr j -
        coPoissonQuotientInverse a r ha hr j
          (coPoissonLadderDefect w hlo hhi a r ha hr (j + 1)) := by
  have hsplit := soninLadderKernel_eq_add_defect (w := w) (hlo := hlo) (hhi := hhi)
    (ha := ha) (hr := hr) (j + 1)
  have hmap := coPoissonQuotientInverse_soninLadderKernel (hlo := hlo) (hhi := hhi)
    (ha := ha) (hr := hr) hr1 j
  rw [hsplit, map_add] at hmap
  rw [← hmap]
  abel

/-- On the annihilator locus the co-Poisson source defect vanishes. -/
theorem coPoissonLadderDefect_eq_zero_of_annihilator {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (j : ℕ) :
    coPoissonLadderDefect w hlo hhi a r ha hr j = 0 :=
  (burnolCoPoissonSourceProjection_eq_zero_iff (soninAperture a r j)).mpr
    (burnolExtendedSoninEvaluationVector_mem_source_orthogonal hlo hhi
      (soninAperture_pos ha hr j) (hann j))

/-- **The forward bonding character on the annihilator boundary.** -/
theorem coPoissonQuotientForward_ladderKernel {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (j : ℕ) :
    coPoissonQuotientForward a r ha hr j (coPoissonLadderKernel w hlo hhi a r ha hr (j + 1)) =
      (starRingEnd ℂ) (soninLadderCharacter w r) • coPoissonLadderKernel w hlo hhi a r ha hr j := by
  rw [coPoissonQuotientForward_ladderKernel_offDivisor hr1 j,
    coPoissonLadderDefect_eq_zero_of_annihilator hann (j + 1), map_zero, sub_zero]

/-- **The inverse bonding character on the annihilator boundary.** -/
theorem coPoissonQuotientInverse_ladderKernel {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (j : ℕ) :
    coPoissonQuotientInverse a r ha hr j (coPoissonLadderKernel w hlo hhi a r ha hr (j + 1)) =
      (starRingEnd ℂ) ((soninLadderCharacter w r)⁻¹) •
        coPoissonLadderKernel w hlo hhi a r ha hr j := by
  rw [coPoissonQuotientInverse_ladderKernel_offDivisor hr1 j,
    coPoissonLadderDefect_eq_zero_of_annihilator hann (j + 1), map_zero, sub_zero]

/-! ## The forced escape law -/


/-- One forward step of the ladder cannot shrink the kernel by more than the character. -/
theorem norm_coPoissonLadderKernel_forward_step {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (j : ℕ) :
    ‖soninLadderCharacter w r‖ * ‖coPoissonLadderKernel w hlo hhi a r ha hr j‖ ≤
      ‖coPoissonLadderKernel w hlo hhi a r ha hr (j + 1)‖ := by
  have hcontr := norm_coPoissonQuotientForward_apply_le a r ha hr j
    (coPoissonLadderKernel w hlo hhi a r ha hr (j + 1))
  rw [coPoissonQuotientForward_ladderKernel hr1 hann j, norm_smul] at hcontr
  simpa using hcontr

/-- One inverse step of the ladder cannot shrink the kernel by more than the inverse character. -/
theorem norm_coPoissonLadderKernel_inverse_step {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (j : ℕ) :
    ‖soninLadderCharacter w r‖⁻¹ * ‖coPoissonLadderKernel w hlo hhi a r ha hr j‖ ≤
      ‖coPoissonLadderKernel w hlo hhi a r ha hr (j + 1)‖ := by
  have hcontr := norm_coPoissonQuotientInverse_apply_le a r ha hr j
    (coPoissonLadderKernel w hlo hhi a r ha hr (j + 1))
  rw [coPoissonQuotientInverse_ladderKernel hr1 hann j, norm_smul] at hcontr
  simpa [norm_inv] using hcontr

/-- Iterating the forward step: the ladder kernel grows at least like the character. -/
theorem norm_coPoissonLadderKernel_geometric_forward {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (N : ℕ) :
    ‖soninLadderCharacter w r‖ ^ N * ‖coPoissonLadderKernel w hlo hhi a r ha hr 0‖ ≤
      ‖coPoissonLadderKernel w hlo hhi a r ha hr N‖ := by
  induction N with
  | zero => simp
  | succ n ih =>
      have hstep := norm_coPoissonLadderKernel_forward_step hr1 hann n
      have hmul : ‖soninLadderCharacter w r‖ *
          (‖soninLadderCharacter w r‖ ^ n * ‖coPoissonLadderKernel w hlo hhi a r ha hr 0‖) ≤
          ‖soninLadderCharacter w r‖ * ‖coPoissonLadderKernel w hlo hhi a r ha hr n‖ :=
        mul_le_mul_of_nonneg_left ih (norm_nonneg _)
      calc ‖soninLadderCharacter w r‖ ^ (n + 1) *
            ‖coPoissonLadderKernel w hlo hhi a r ha hr 0‖
          = ‖soninLadderCharacter w r‖ *
            (‖soninLadderCharacter w r‖ ^ n *
              ‖coPoissonLadderKernel w hlo hhi a r ha hr 0‖) := by ring
        _ ≤ ‖soninLadderCharacter w r‖ * ‖coPoissonLadderKernel w hlo hhi a r ha hr n‖ := hmul
        _ ≤ ‖coPoissonLadderKernel w hlo hhi a r ha hr (n + 1)‖ := hstep

/-- Iterating the inverse step: the ladder kernel grows at least like the inverse character. -/
theorem norm_coPoissonLadderKernel_geometric_inverse {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (N : ℕ) :
    (‖soninLadderCharacter w r‖⁻¹) ^ N * ‖coPoissonLadderKernel w hlo hhi a r ha hr 0‖ ≤
      ‖coPoissonLadderKernel w hlo hhi a r ha hr N‖ := by
  induction N with
  | zero => simp
  | succ n ih =>
      have hstep := norm_coPoissonLadderKernel_inverse_step hr1 hann n
      have hmul : ‖soninLadderCharacter w r‖⁻¹ *
          ((‖soninLadderCharacter w r‖⁻¹) ^ n *
            ‖coPoissonLadderKernel w hlo hhi a r ha hr 0‖) ≤
          ‖soninLadderCharacter w r‖⁻¹ * ‖coPoissonLadderKernel w hlo hhi a r ha hr n‖ :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      calc (‖soninLadderCharacter w r‖⁻¹) ^ (n + 1) *
            ‖coPoissonLadderKernel w hlo hhi a r ha hr 0‖
          = ‖soninLadderCharacter w r‖⁻¹ *
            ((‖soninLadderCharacter w r‖⁻¹) ^ n *
              ‖coPoissonLadderKernel w hlo hhi a r ha hr 0‖) := by ring
        _ ≤ ‖soninLadderCharacter w r‖⁻¹ * ‖coPoissonLadderKernel w hlo hhi a r ha hr n‖ := hmul
        _ ≤ ‖coPoissonLadderKernel w hlo hhi a r ha hr (n + 1)‖ := hstep

/-- **The sharp forced escape law.**  The ladder kernel escapes at the exact two-sided geometric
rate given by the character. -/
theorem norm_coPoissonLadderKernel_max_le {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (N : ℕ) :
    max (‖soninLadderCharacter w r‖ ^ N) ((‖soninLadderCharacter w r‖⁻¹) ^ N) *
        ‖coPoissonLadderKernel w hlo hhi a r ha hr 0‖ ≤
      ‖coPoissonLadderKernel w hlo hhi a r ha hr N‖ := by
  rcases max_cases (‖soninLadderCharacter w r‖ ^ N) ((‖soninLadderCharacter w r‖⁻¹) ^ N) with
    ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; exact norm_coPoissonLadderKernel_geometric_forward hr1 hann N
  · rw [h]; exact norm_coPoissonLadderKernel_geometric_inverse hr1 hann N

/-! ## The independent-quadrant section -/

/-- The quadrant coordinate `X_{p,q} = conj(λ)^{q-p} y_{w,p+q}`. -/
def coPoissonQuadrantCoordinate (w : ℂ) (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (p q : ℕ) : evenSubspace :=
  ((starRingEnd ℂ) (soninLadderCharacter w r)) ^ ((q : ℤ) - (p : ℤ)) •
    coPoissonLadderKernel w hlo hhi a r ha hr (p + q)

@[simp] theorem coPoissonQuadrantCoordinate_zero_zero (w : ℂ) (hlo : 1 / 2 < w.re)
    (hhi : w.re < 1) (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    coPoissonQuadrantCoordinate w hlo hhi a r ha hr 0 0 =
      coPoissonLadderKernel w hlo hhi a r ha hr 0 := by
  simp [coPoissonQuadrantCoordinate]

/-- **The forward projective bonding law.**  `T^+_{p+q} X_{p+1,q} = X_{p,q}`. -/
theorem coPoissonQuotientForward_quadrantCoordinate {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (p q : ℕ) :
    coPoissonQuotientForward a r ha hr (p + q)
        (coPoissonQuadrantCoordinate w hlo hhi a r ha hr (p + 1) q) =
      coPoissonQuadrantCoordinate w hlo hhi a r ha hr p q := by
  have hne : ((starRingEnd ℂ) (soninLadderCharacter w r)) ≠ 0 := by
    simpa using soninLadderCharacter_ne_zero hr w
  have hidx : p + 1 + q = (p + q) + 1 := by omega
  rw [coPoissonQuadrantCoordinate, coPoissonQuadrantCoordinate, hidx,
    ContinuousLinearMap.map_smul, coPoissonQuotientForward_ladderKernel hr1 hann (p + q),
    smul_smul]
  congr 1
  rw [← zpow_add_one₀ hne]
  congr 1
  push_cast
  ring

/-- **The inverse projective bonding law.**  `T^-_{p+q} X_{p,q+1} = X_{p,q}`. -/
theorem coPoissonQuotientInverse_quadrantCoordinate {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (p q : ℕ) :
    coPoissonQuotientInverse a r ha hr (p + q)
        (coPoissonQuadrantCoordinate w hlo hhi a r ha hr p (q + 1)) =
      coPoissonQuadrantCoordinate w hlo hhi a r ha hr p q := by
  have hne : ((starRingEnd ℂ) (soninLadderCharacter w r)) ≠ 0 := by
    simpa using soninLadderCharacter_ne_zero hr w
  have hidx : p + (q + 1) = (p + q) + 1 := by omega
  rw [coPoissonQuadrantCoordinate, coPoissonQuadrantCoordinate, hidx,
    ContinuousLinearMap.map_smul, coPoissonQuotientInverse_ladderKernel hr1 hann (p + q),
    smul_smul]
  congr 1
  rw [map_inv₀, ← zpow_neg_one ((starRingEnd ℂ) (soninLadderCharacter w r)),
    ← zpow_add₀ hne]
  congr 1
  push_cast
  ring

/-- **The commuting quadrant square, forward-then-inverse.** -/
theorem coPoissonQuadrant_square_forward_inverse {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (p q : ℕ) :
    coPoissonQuotientForward a r ha hr (p + q)
        (coPoissonQuotientInverse a r ha hr (p + q + 1)
          (coPoissonQuadrantCoordinate w hlo hhi a r ha hr (p + 1) (q + 1))) =
      coPoissonQuadrantCoordinate w hlo hhi a r ha hr p q := by
  have hstep := coPoissonQuotientInverse_quadrantCoordinate hr1 hann (p + 1) q
  have hidx : p + 1 + q = p + q + 1 := by omega
  rw [hidx] at hstep
  rw [hstep]
  exact coPoissonQuotientForward_quadrantCoordinate hr1 hann p q

/-- **The commuting quadrant square, inverse-then-forward.** -/
theorem coPoissonQuadrant_square_inverse_forward {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (p q : ℕ) :
    coPoissonQuotientInverse a r ha hr (p + q)
        (coPoissonQuotientForward a r ha hr (p + q + 1)
          (coPoissonQuadrantCoordinate w hlo hhi a r ha hr (p + 1) (q + 1))) =
      coPoissonQuadrantCoordinate w hlo hhi a r ha hr p q := by
  have hstep := coPoissonQuotientForward_quadrantCoordinate hr1 hann p (q + 1)
  have hidx : p + (q + 1) = p + q + 1 := by omega
  rw [hidx] at hstep
  rw [hstep]
  exact coPoissonQuotientInverse_quadrantCoordinate hr1 hann p q

/-- The two paths around a quadrant square agree on the section. -/
theorem coPoissonQuadrant_square_comm {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (p q : ℕ) :
    coPoissonQuotientForward a r ha hr (p + q)
        (coPoissonQuotientInverse a r ha hr (p + q + 1)
          (coPoissonQuadrantCoordinate w hlo hhi a r ha hr (p + 1) (q + 1))) =
      coPoissonQuotientInverse a r ha hr (p + q)
        (coPoissonQuotientForward a r ha hr (p + q + 1)
          (coPoissonQuadrantCoordinate w hlo hhi a r ha hr (p + 1) (q + 1))) := by
  rw [coPoissonQuadrant_square_forward_inverse hr1 hann p q,
    coPoissonQuadrant_square_inverse_forward hr1 hann p q]

/-- **The quadrant escape bound.**  Every quadrant coordinate escapes at the exact rate given by
the character in one of the two independent faces. -/
theorem norm_coPoissonQuadrantCoordinate_escape {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (p q : ℕ) :
    max (‖soninLadderCharacter w r‖ ^ (2 * (q : ℤ)))
        (‖soninLadderCharacter w r‖ ^ (-(2 * (p : ℤ)))) *
        ‖coPoissonQuadrantCoordinate w hlo hhi a r ha hr 0 0‖ ≤
      ‖coPoissonQuadrantCoordinate w hlo hhi a r ha hr p q‖ := by
  set L := ‖soninLadderCharacter w r‖ with hLdef
  have hL : 0 < L := norm_soninLadderCharacter_pos hr w
  have hXnorm : ‖coPoissonQuadrantCoordinate w hlo hhi a r ha hr p q‖ =
      L ^ ((q : ℤ) - (p : ℤ)) * ‖coPoissonLadderKernel w hlo hhi a r ha hr (p + q)‖ := by
    rw [coPoissonQuadrantCoordinate, norm_smul, norm_zpow, hLdef]
    simp
  have h00 : ‖coPoissonQuadrantCoordinate w hlo hhi a r ha hr 0 0‖ =
      ‖coPoissonLadderKernel w hlo hhi a r ha hr 0‖ := by
    rw [coPoissonQuadrantCoordinate_zero_zero]
  have hgeo := norm_coPoissonLadderKernel_max_le hr1 hann (p + q)
  have hpow : max (L ^ (2 * (q : ℤ))) (L ^ (-(2 * (p : ℤ)))) =
      L ^ ((q : ℤ) - (p : ℤ)) * max (L ^ (p + q)) ((L⁻¹) ^ (p + q)) := by
    have hnat : L ^ (p + q) = L ^ ((p : ℤ) + (q : ℤ)) := by
      rw [← zpow_natCast L (p + q)]
      norm_num
    have hinv : (L⁻¹) ^ (p + q) = L ^ (-((p : ℤ) + (q : ℤ))) := by
      rw [inv_pow, hnat, zpow_neg]
    rw [hinv, hnat, mul_max_of_nonneg _ _ (le_of_lt (zpow_pos hL _)),
      ← zpow_add₀ hL.ne', ← zpow_add₀ hL.ne']
    congr 2 <;> ring
  rw [hXnorm, h00, hpow, mul_assoc]
  exact mul_le_mul_of_nonneg_left hgeo (le_of_lt (zpow_pos hL _))

end RHTower
