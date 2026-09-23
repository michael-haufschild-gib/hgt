import GaloisForLFunctions.HTGeometry.SelfAdjointResolvent
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenvalue

/-!
# The resolvent of a self-adjoint operator, and compactness

At a nonreal parameter the shifted operator is a bijection of the domain onto the space with a
two-sided bound, so its inverse is a bounded operator: the resolvent.  An eigenvector of the
resolvent with nonzero eigenvalue is an eigenvector of the operator, so an operator without
eigenvectors has an eigenvector-free resolvent.
-/

open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The shifted operator as a linear equivalence of the domain with the whole space. -/
def shiftedEquiv {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    A.domain ≃ₗ[ℂ] H :=
  LinearEquiv.ofBijective (shiftedMap A z) (bijective_shiftedMap hA hz)

@[simp] theorem shiftedEquiv_apply {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) (x : A.domain) : shiftedEquiv hA hz x = A x - z • (x : H) := rfl

/-- The resolvent as a linear map. -/
def resolventLinear {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    H →ₗ[ℂ] H :=
  A.domain.subtype ∘ₗ (shiftedEquiv hA hz).symm.toLinearMap

theorem resolventLinear_mem {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0)
    (y : H) : resolventLinear hA hz y ∈ A.domain :=
  ((shiftedEquiv hA hz).symm y).2

/-- The defining property of the resolvent. -/
theorem shiftedMap_resolventLinear {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) (y : H) :
    A ⟨resolventLinear hA hz y, resolventLinear_mem hA hz y⟩ -
      z • resolventLinear hA hz y = y := by
  have h := (shiftedEquiv hA hz).apply_symm_apply y
  rw [shiftedEquiv_apply] at h
  exact h

theorem norm_resolventLinear_le {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) (y : H) : ‖resolventLinear hA hz y‖ ≤ |z.im|⁻¹ * ‖y‖ := by
  have habs : 0 < |z.im| := abs_pos.2 hz
  have hlow := norm_sub_smul_lower_bound hA z ((shiftedEquiv hA hz).symm y)
  have hval : A ((shiftedEquiv hA hz).symm y) -
      z • (((shiftedEquiv hA hz).symm y : A.domain) : H) = y :=
    shiftedMap_resolventLinear hA hz y
  rw [hval] at hlow
  rw [inv_mul_eq_div, le_div_iff₀ habs, mul_comm]
  exact hlow

/-- **The resolvent.**  At a nonreal parameter the inverse of the shifted operator is bounded. -/
def resolventCLM {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) : H →L[ℂ] H :=
  (resolventLinear hA hz).mkContinuous |z.im|⁻¹ (norm_resolventLinear_le hA hz)

@[simp] theorem resolventCLM_apply {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) (y : H) : resolventCLM hA hz y = resolventLinear hA hz y := rfl

theorem resolventCLM_injective {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) : Function.Injective (resolventCLM hA hz) := by
  intro a b hab
  have h : ((shiftedEquiv hA hz).symm a : A.domain) = (shiftedEquiv hA hz).symm b :=
    Subtype.ext hab
  have := congrArg (shiftedEquiv hA hz) h
  rwa [(shiftedEquiv hA hz).apply_symm_apply, (shiftedEquiv hA hz).apply_symm_apply] at this

/-- **An eigenvector of the resolvent is an eigenvector of the operator.** -/
theorem hasEigenvector_of_resolvent {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) {lam : ℂ} (hlam : lam ≠ 0) {v : H} (hv : resolventCLM hA hz v = lam • v) :
    ∃ hmem : v ∈ A.domain, A ⟨v, hmem⟩ = (z + lam⁻¹) • v := by
  have hmemlam : lam • v ∈ A.domain := by
    rw [← hv]
    exact resolventLinear_mem hA hz v
  have hmem : v ∈ A.domain := by
    have := A.domain.smul_mem lam⁻¹ hmemlam
    rwa [smul_smul, inv_mul_cancel₀ hlam, one_smul] at this
  refine ⟨hmem, ?_⟩
  have hkey := shiftedMap_resolventLinear hA hz v
  have hcoe : (⟨resolventLinear hA hz v, resolventLinear_mem hA hz v⟩ : A.domain) =
      lam • (⟨v, hmem⟩ : A.domain) := by
    apply Subtype.ext
    simpa using hv
  have hv' : resolventLinear hA hz v = lam • v := hv
  rw [hcoe, A.map_smul, hv'] at hkey
  have hsmul : lam • A (⟨v, hmem⟩ : A.domain) = v + z • (lam • v) := by
    have := hkey
    rw [sub_eq_iff_eq_add] at this
    exact this
  have hAv : A (⟨v, hmem⟩ : A.domain) = lam⁻¹ • (v + z • (lam • v)) := by
    rw [← hsmul, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  rw [hAv, smul_add, smul_smul, smul_smul,
    show lam⁻¹ * z * lam = z from by field_simp]
  module

/-- **An eigenvector-free operator has an eigenvector-free resolvent.** -/
theorem resolvent_no_eigenvector {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hno : HasNoEigenvector A) {z : ℂ} (hz : z.im ≠ 0) {lam : ℂ} {v : H}
    (hv : resolventCLM hA hz v = lam • v) : v = 0 := by
  rcases eq_or_ne lam 0 with rfl | hlam
  · rw [zero_smul] at hv
    have : resolventCLM hA hz v = resolventCLM hA hz 0 := by
      rw [hv, map_zero]
    exact resolventCLM_injective hA hz this
  · obtain ⟨hmem, hAv⟩ := hasEigenvector_of_resolvent hA hz hlam hv
    exact hno (z + lam⁻¹) ⟨v, hmem⟩ hAv

/-! ## The adjoint of the resolvent -/

/-- **The resolvent pairing.**  The resolvent at `z` and at the conjugate parameter are formal
adjoints of each other. -/
theorem inner_resolventCLM {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) (hzw : w = (starRingEnd ℂ) z) (x y : H) :
    inner ℂ (resolventCLM hA hz x) y = inner ℂ x (resolventCLM hA hw y) := by
  have hu := shiftedMap_resolventLinear hA hz x
  have hv := shiftedMap_resolventLinear hA hw y
  set u : H := resolventLinear hA hz x with hudef
  set v : H := resolventLinear hA hw y with hvdef
  have humem : u ∈ A.domain := resolventLinear_mem hA hz x
  have hvmem : v ∈ A.domain := resolventLinear_mem hA hw y
  have hsym := isFormalAdjoint_of_isSelfAdjoint hA ⟨u, humem⟩ ⟨v, hvmem⟩
  show inner ℂ u y = inner ℂ x v
  have hleft : inner ℂ u y =
      inner ℂ u (A ⟨v, hvmem⟩) - w * inner ℂ u v := by
    rw [← hv, inner_sub_right, inner_smul_right]
  have hright : inner ℂ x v =
      inner ℂ (A ⟨u, humem⟩) v - (starRingEnd ℂ) z * inner ℂ u v := by
    rw [← hu, inner_sub_left, inner_smul_left]
  rw [hleft, hright, hzw, ← hsym]

/-- **The adjoint of the resolvent is the resolvent at the conjugate parameter.** -/
theorem adjoint_resolventCLM {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) (hzw : w = (starRingEnd ℂ) z) :
    ContinuousLinearMap.adjoint (resolventCLM hA hz) = resolventCLM hA hw := by
  have hzc : z = (starRingEnd ℂ) w := by
    rw [hzw]
    simp
  exact ((ContinuousLinearMap.eq_adjoint_iff (resolventCLM hA hw)
    (resolventCLM hA hz)).2 fun x y => inner_resolventCLM hA hw hz hzc x y).symm

/-! ## No compact resolvent without eigenvectors -/

/-- **An eigenvector-free self-adjoint operator has no compact resolvent.**  This is the
elementary form of the compact-perturbation exclusion: it needs no essential spectrum. -/
theorem not_isCompactOperator_resolventCLM {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hno : HasNoEigenvector A) [Nontrivial H] {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) (hzw : w = (starRingEnd ℂ) z) :
    ¬ IsCompactOperator (resolventCLM hA hz) := by
  intro hcpt
  set R : H →L[ℂ] H := resolventCLM hA hz with hR
  set R' : H →L[ℂ] H := resolventCLM hA hw with hR'
  set S : H →L[ℂ] H := R' ∘L R with hS
  -- `S` is the compact positive operator `R* R`
  have hadj : ContinuousLinearMap.adjoint R = R' := adjoint_resolventCLM hA hz hw hzw
  have hSinner : ∀ x y : H, inner ℂ (S x) y = inner ℂ (R x) (R y) := by
    intro x y
    rw [hS, ContinuousLinearMap.comp_apply, ← hadj,
      ContinuousLinearMap.adjoint_inner_left]
  have hSsym : S.IsSymmetric := by
    intro x y
    show inner ℂ (S x) y = inner ℂ x (S y)
    have h1 : inner ℂ x (S y) = (starRingEnd ℂ) (inner ℂ (S y) x) :=
      (inner_conj_symm x (S y)).symm
    rw [hSinner x y, h1, hSinner y x, inner_conj_symm]
  have hScpt : IsCompactOperator S := hcpt.clm_comp R'
  have hSne : S ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have hzero : inner ℂ (R x) (R x) = 0 := by
      rw [← hSinner x x, h0]
      simp
    have hRx : R x = 0 := inner_self_eq_zero.1 hzero
    exact hx (resolventCLM_injective hA hz (by rw [← hR, hRx, map_zero]))
  obtain ⟨mu, v, hmuNorm, hvnorm, hSv⟩ :=
    ContinuousLinearMap.exists_unit_eigenvector_norm hScpt hSsym hSne
  -- the eigenvalue is the squared norm of `R v`
  have hvv : inner ℂ v v = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hvnorm]
    norm_num
  have hmu_eq : (mu : ℂ) = inner ℂ (R v) (R v) := by
    have h1 : inner ℂ (S v) v = inner ℂ (R v) (R v) := hSinner v v
    rw [hSv, inner_smul_left, hvv, mul_one, Complex.conj_ofReal] at h1
    exact h1
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hvnorm
    exact zero_ne_one hvnorm
  have hRv0 : R v ≠ 0 := fun h0 => hv0 (resolventCLM_injective hA hz (by rw [← hR, h0, map_zero]))
  have hmunorm : (mu : ℝ) = ‖R v‖ ^ (2 : ℕ) := by
    have h2 : ((mu : ℝ) : ℂ) = ((‖R v‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [hmu_eq, inner_self_eq_norm_sq_to_K]
      simp
    exact_mod_cast h2
  have hmupos : 0 < mu := by
    have hne : (mu : ℂ) ≠ 0 := by
      rw [hmu_eq]
      exact fun h => hRv0 (inner_self_eq_zero.1 h)
    have hnn : (0 : ℝ) ≤ mu := by
      rw [hmunorm]
      positivity
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [← h]; norm_num) hne
  have hmuC : (mu : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hmupos.ne'
  -- the eigenvector lies in the domain
  have hSveq : resolventLinear hA hw (R v) = (mu : ℂ) • v := hSv
  have hmuvmem : (mu : ℂ) • v ∈ A.domain := by
    rw [← hSveq]
    exact resolventLinear_mem hA hw (R v)
  have hvmem : v ∈ A.domain := by
    have := A.domain.smul_mem ((mu : ℂ)⁻¹) hmuvmem
    rwa [smul_smul, inv_mul_cancel₀ hmuC, one_smul] at this
  have hRvmem : R v ∈ A.domain := resolventLinear_mem hA hz v
  -- the first resolvent equation
  have hstep1 : R v = (mu : ℂ) • (A ⟨v, hvmem⟩ - w • v) := by
    have hkey := shiftedMap_resolventLinear hA hw (R v)
    have hcoe : (⟨resolventLinear hA hw (R v), resolventLinear_mem hA hw (R v)⟩ : A.domain) =
        (mu : ℂ) • (⟨v, hvmem⟩ : A.domain) := by
      apply Subtype.ext
      simpa using hSveq
    rw [hcoe, A.map_smul, hSveq] at hkey
    rw [← hkey, smul_sub, smul_smul, smul_smul, mul_comm]
  -- so `A v` lies in the domain
  have hAvmem : (A ⟨v, hvmem⟩ : H) ∈ A.domain := by
    have hsub : A ⟨v, hvmem⟩ - w • v = ((mu : ℂ)⁻¹) • R v := by
      rw [hstep1, smul_smul, inv_mul_cancel₀ hmuC, one_smul]
    have hmem : A ⟨v, hvmem⟩ - w • v ∈ A.domain := by
      rw [hsub]
      exact A.domain.smul_mem _ hRvmem
    have := A.domain.add_mem hmem (A.domain.smul_mem w hvmem)
    simpa using this
  set p : H := A ⟨v, hvmem⟩ with hp
  -- the second resolvent equation
  have hstep2 : A ⟨p, hAvmem⟩ = (w + z) • p + ((mu : ℂ)⁻¹ - z * w) • v := by
    have hkey := shiftedMap_resolventLinear hA hz v
    have hstep1' : resolventLinear hA hz v = (mu : ℂ) • (p - w • v) := hstep1
    have hcoe : (⟨resolventLinear hA hz v, resolventLinear_mem hA hz v⟩ : A.domain) =
        (mu : ℂ) • ((⟨p, hAvmem⟩ : A.domain) - w • (⟨v, hvmem⟩ : A.domain)) := by
      apply Subtype.ext
      simpa using hstep1'
    rw [hcoe, A.map_smul, A.map_sub, A.map_smul, hstep1'] at hkey
    have hcancel : (mu : ℂ) • (A ⟨p, hAvmem⟩ - w • p) =
        v + z • ((mu : ℂ) • (p - w • v)) := sub_eq_iff_eq_add.1 hkey
    have hmul : ((mu : ℂ)⁻¹) • ((mu : ℂ) • (A ⟨p, hAvmem⟩ - w • p)) =
        A ⟨p, hAvmem⟩ - w • p := by
      rw [smul_smul, inv_mul_cancel₀ hmuC, one_smul]
    have hzsimp : ((mu : ℂ)⁻¹) • (z • ((mu : ℂ) • (p - w • v))) = z • (p - w • v) := by
      rw [smul_smul, smul_smul]
      congr 1
      field_simp
    have h2 : A ⟨p, hAvmem⟩ - w • p = ((mu : ℂ)⁻¹) • v + z • (p - w • v) := by
      rw [← hmul, hcancel, smul_add, hzsimp]
    rw [sub_eq_iff_eq_add] at h2
    rw [h2]
    module
  -- the real coordinates
  have hwz : w + z = ((2 * z.re : ℝ) : ℂ) := by
    rw [hzw, add_comm, Complex.add_conj]
  have hzw' : z * w = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [hzw, Complex.mul_conj]
  have hnormSq : Complex.normSq z = z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by
    rw [Complex.normSq_apply]
    ring
  -- the imaginary lower bound bounds the eigenvalue
  have hd : 0 ≤ (mu : ℝ)⁻¹ - z.im ^ (2 : ℕ) := by
    have hlow := norm_sub_smul_lower_bound hA z ⟨R v, hRvmem⟩
    have hval : A (⟨R v, hRvmem⟩ : A.domain) - z • (R v) = v :=
      shiftedMap_resolventLinear hA hz v
    rw [hval, hvnorm] at hlow
    have h3 : 0 ≤ |z.im| * ‖R v‖ := by positivity
    have hsq : z.im ^ (2 : ℕ) * mu ≤ 1 := by
      rw [hmunorm]
      nlinarith [sq_abs z.im, hlow, h3]
    have hinv : mu * (mu : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hmupos.ne'
    have hipos : (0 : ℝ) < (mu : ℝ)⁻¹ := inv_pos.2 hmupos
    nlinarith [hsq, hmupos, hipos, hinv]
  obtain ⟨c, hc2⟩ : ∃ c : ℝ, c ^ (2 : ℕ) = (mu : ℝ)⁻¹ - z.im ^ (2 : ℕ) :=
    ⟨Real.sqrt ((mu : ℝ)⁻¹ - z.im ^ (2 : ℕ)), Real.sq_sqrt hd⟩
  -- the factorized eigenvector
  set u : H := p - (((z.re : ℝ) : ℂ) - ((c : ℝ) : ℂ)) • v with hu
  have humem : u ∈ A.domain := A.domain.sub_mem hAvmem (A.domain.smul_mem _ hvmem)
  have hAu : A ⟨u, humem⟩ = ((((z.re : ℝ) : ℂ) + ((c : ℝ) : ℂ))) • u := by
    have hsplit : (⟨u, humem⟩ : A.domain) =
        (⟨p, hAvmem⟩ : A.domain) - (((z.re : ℝ) : ℂ) - ((c : ℝ) : ℂ)) • (⟨v, hvmem⟩ : A.domain) := by
      apply Subtype.ext
      simpa using hu
    rw [hsplit, A.map_sub, A.map_smul, hstep2]
    rw [hwz]
    rw [hzw']
    rw [hnormSq]
    rw [hu]
    have hcs : ((c : ℝ) : ℂ) ^ (2 : ℕ) = ((mu : ℂ))⁻¹ - ((z.im : ℝ) : ℂ) ^ (2 : ℕ) := by
      have h : (((c ^ (2 : ℕ) : ℝ)) : ℂ) = (((mu : ℝ)⁻¹ - z.im ^ (2 : ℕ) : ℝ) : ℂ) := by rw [hc2]
      push_cast at h
      exact h
    push_cast
    match_scalars
    all_goals (try ring)
    all_goals (rw [hcs]; ring)
  rcases eq_or_ne u 0 with h0 | h0
  · -- the degenerate branch: `v` itself is an eigenvector
    have hAv : A ⟨v, hvmem⟩ = ((((z.re : ℝ) : ℂ) - ((c : ℝ) : ℂ))) • v := by
      have : p - (((z.re : ℝ) : ℂ) - ((c : ℝ) : ℂ)) • v = 0 := h0
      rw [sub_eq_zero] at this
      rw [← hp, this]
    exact hv0 (hno _ ⟨v, hvmem⟩ hAv)
  · exact h0 (hno _ ⟨u, humem⟩ hAu)

/-! ## Bounded perturbations -/

/-- **A bounded perturbation cannot create a compact resolvent.**  If a bounded operator `Q`
inverts `A + K - z` on the domain of an eigenvector-free self-adjoint `A`, with `K` bounded, then
`Q` is not compact.  This is the elementary form of the compact and trace-class exclusions: it uses
the second resolvent identity instead of the invariance of the essential spectrum. -/
theorem not_isCompactOperator_of_boundedPerturbation {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (hno : HasNoEigenvector A) [Nontrivial H] {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzw : w = (starRingEnd ℂ) z) (K Q : H →L[ℂ] H)
    (hQ : ∀ x : A.domain, Q (A x - z • (x : H) + K (x : H)) = (x : H)) :
    ¬ IsCompactOperator Q := by
  intro hQcpt
  refine not_isCompactOperator_resolventCLM hA hno hz hw hzw ?_
  have hid : ∀ y : H, (resolventCLM hA hz y : H) =
      Q y + Q (K (resolventCLM hA hz y)) := by
    intro y
    have hx := hQ ⟨resolventLinear hA hz y, resolventLinear_mem hA hz y⟩
    rw [shiftedMap_resolventLinear hA hz y, map_add] at hx
    exact hx.symm
  have hfun : (⇑(resolventCLM hA hz) : H → H) =
      ⇑Q + (⇑Q ∘ ⇑(K ∘L resolventCLM hA hz)) := by
    funext y
    simpa using hid y
  rw [hfun]
  exact hQcpt.add (hQcpt.comp_clm (K ∘L resolventCLM hA hz))

end GaloisForLFunctions.HTGeometry
