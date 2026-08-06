import GaloisForLFunctions.HTGeometry.FiniteQuditHermitianStringBasis
import GaloisForLFunctions.HTGeometry.ObserverInvisibleRayPreservation

/-!
# The observer-visible rank of a product state under a `q`-local dictionary

The product ground state of a qudit register sees a `q`-local Hermitian string
only through the single configuration obtained by applying the local raising
labels, so the whole non-scalar `q`-local dictionary acts on it with image the
realification of the span of the excitation configurations of weight between `1`
and `q`.  Its real rank is therefore twice the number of such configurations,
and the invisible carrier has the complementary dimension.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {D : ℕ} [NeZero D]

/-- The configuration basis vector. -/
def configBasis (t : σ → Fin D) : (σ → Fin D) → ℂ := Pi.single t (1 : ℂ)

omit [DecidableEq σ] [NeZero D] in
theorem configBasis_apply (t c : σ → Fin D) :
    configBasis t c = if c = t then (1 : ℂ) else 0 := Pi.single_apply _ _ _

/-- The product ground state of the register. -/
def quditVacuum : (σ → Fin D) → ℂ := configBasis (fun _ : σ => 0)

/-- The configuration reached from the ground index by a local label. -/
def localVacTarget (p : Fin D × Fin D) : Fin D :=
  if p.1 = p.2 then 0 else if p.1 = 0 then p.2 else if p.2 = 0 then p.1 else 0

/-- The amplitude with which a local label reaches its target from the ground
index. -/
noncomputable def localVacCoeff (p : Fin D × Fin D) : ℂ :=
  if p.1 = p.2 then (if p.1 = 0 then 1 else -1)
  else if p.1 = 0 then 1 else if p.2 = 0 then Complex.I else 0

/-- **Local ground action.**  Every local Hermitian unit sends the ground index to
a multiple of a single index. -/
theorem quditHermUnit_apply_ground (p : Fin D × Fin D) (r : Fin D) :
    quditHermUnit p r 0
      = localVacCoeff p * (if r = localVacTarget p then (1 : ℂ) else 0) := by
  rcases eq_or_ne p.1 p.2 with hd | hd
  · rcases eq_or_ne p.1 0 with h0 | h0
    · have hp : p = (0, 0) := Prod.ext h0 (hd ▸ h0)
      rw [hp, quditHermUnit_zero]
      simp [localVacCoeff, localVacTarget, Matrix.one_apply]
    · have hp : p = (p.1, p.1) := Prod.ext rfl hd.symm
      rw [hp, quditHermUnit_diag_of_ne_zero h0]
      by_cases hr : r = (0 : Fin D) <;>
        simp [Matrix.sub_apply, localVacCoeff, localVacTarget, h0, hr, eq_comm]
  · rcases lt_or_gt_of_ne hd with hlt | hgt
    · have h2ne : p.2 ≠ 0 := (lt_of_le_of_lt (Fin.zero_le p.1) hlt).ne'
      rw [show p = (p.1, p.2) from rfl, quditHermUnit_lt hlt]
      simp only [Matrix.add_apply, Matrix.single_apply, localVacCoeff, localVacTarget,
        if_neg hd]
      rcases eq_or_ne p.1 0 with h0 | h0
      · simp [h0, h2ne, eq_comm]
      · simp [h0, h2ne]
    · have h1ne : p.1 ≠ 0 := (lt_of_le_of_lt (Fin.zero_le p.2) hgt).ne'
      rw [show p = (p.1, p.2) from rfl, quditHermUnit_gt hgt]
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul,
        localVacCoeff, localVacTarget, if_neg hd, if_neg h1ne]
      rcases eq_or_ne p.2 0 with h2 | h2
      · simp [h2, h1ne, eq_comm]
      · simp [h2, h1ne]

/-- The configuration a string label reaches from the product ground state. -/
def stringVacTarget (a : σ → Fin D × Fin D) : σ → Fin D :=
  fun i => localVacTarget (a i)

/-- The amplitude with which a string label reaches its target. -/
noncomputable def stringVacCoeff (a : σ → Fin D × Fin D) : ℂ :=
  ∏ i, localVacCoeff (a i)

/-- **Product ground action.**  A Hermitian string sends the product ground state
to a multiple of a single configuration basis vector. -/
theorem quditString_mulVec_vacuum (a : σ → Fin D × Fin D) :
    quditString a *ᵥ (quditVacuum : (σ → Fin D) → ℂ)
      = stringVacCoeff a • configBasis (stringVacTarget a) := by
  funext r
  have hlhs : (quditString a *ᵥ (quditVacuum : (σ → Fin D) → ℂ)) r
      = quditString a r (fun _ => 0) := by
    simp only [Matrix.mulVec, dotProduct, quditVacuum, configBasis_apply]
    rw [Finset.sum_eq_single (fun _ : σ => (0 : Fin D))
      (fun b _ hb => by rw [if_neg hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, mul_one]
  rw [hlhs, Pi.smul_apply, configBasis_apply, smul_eq_mul, quditString_apply]
  simp only [stringVacCoeff]
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    quditHermUnit_apply_ground (a i) (r i))]
  rw [Finset.prod_mul_distrib, Finset.prod_boole]
  refine congrArg _ ?_
  by_cases h : r = stringVacTarget a
  · rw [if_pos h, if_pos (show ∀ i ∈ Finset.univ, r i = localVacTarget (a i) from
      fun i _ => congrFun h i)]
  · rw [if_neg h, if_neg (show ¬ ∀ i ∈ Finset.univ, r i = localVacTarget (a i) from
      fun hh => h (funext fun i => hh i (Finset.mem_univ i)))]


section VacuumAction

/-- Pairing against the product ground state evaluates at the ground
configuration. -/
theorem star_quditVacuum_dotProduct (v : (σ → Fin D) → ℂ) :
    star (quditVacuum : (σ → Fin D) → ℂ) ⬝ᵥ v = v (fun _ => 0) := by
  simp only [dotProduct, quditVacuum, configBasis_apply, Pi.star_apply]
  rw [Finset.sum_eq_single (fun _ : σ => (0 : Fin D))
    (fun b _ hb => by rw [if_neg hb]; simp)
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [if_pos rfl]
  simp

/-- The expectation of a Hermitian string in the product ground state. -/
theorem expval_quditString_vacuum (a : σ → Fin D × Fin D) :
    QuantumAlg.expval (quditVacuum : (σ → Fin D) → ℂ) (quditString a)
      = stringVacCoeff a *
        (if (fun _ : σ => (0 : Fin D)) = stringVacTarget a then (1 : ℂ) else 0) := by
  rw [QuantumAlg.expval, quditString_mulVec_vacuum, star_quditVacuum_dotProduct,
    Pi.smul_apply, configBasis_apply, smul_eq_mul]

/-- **Centered ground action.**  A Hermitian string is invisible to the product
ground state exactly when it does not move the ground configuration; otherwise it
produces the corresponding excitation direction. -/
theorem centered_quditString_vacuum (a : σ → Fin D × Fin D) :
    QuantumAlg.centered (quditVacuum : (σ → Fin D) → ℂ) (quditString a)
      = if stringVacTarget a = (fun _ : σ => 0) then 0
        else stringVacCoeff a • configBasis (stringVacTarget a) := by
  rw [QuantumAlg.centered, quditString_mulVec_vacuum, expval_quditString_vacuum]
  by_cases h : stringVacTarget a = (fun _ : σ => 0)
  · rw [if_pos h, if_pos h.symm, mul_one, h]
    simp [quditVacuum]
  · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero, zero_smul, sub_zero]

end VacuumAction

section Witnesses

omit [DecidableEq σ] in
/-- The excitation support of the configuration a string reaches is contained in
the support of the string. -/
theorem configSupport_stringVacTarget_subset (a : σ → Fin D × Fin D) :
    configSupport (0 : Fin D) (stringVacTarget a) ⊆ quditStringSupport a := by
  intro i hi
  rw [mem_quditStringSupport]
  intro hcontra
  rw [mem_configSupport] at hi
  exact hi (by simp [stringVacTarget, hcontra, localVacTarget])

/-- The label producing a real excitation direction. -/
def realWitnessLabel (c : σ → Fin D) : σ → Fin D × Fin D :=
  fun i => if c i = 0 then (0, 0) else (0, c i)

/-- The label producing an imaginary excitation direction. -/
def imagWitnessLabel (c : σ → Fin D) (i₀ : σ) : σ → Fin D × Fin D :=
  fun i => if i = i₀ then (c i₀, 0) else (if c i = 0 then (0, 0) else (0, c i))

omit [DecidableEq σ] in
theorem quditStringSupport_realWitnessLabel (c : σ → Fin D) :
    quditStringSupport (realWitnessLabel c) = configSupport (0 : Fin D) c := by
  ext i
  rw [mem_quditStringSupport, mem_configSupport]
  by_cases h : c i = 0 <;> simp [realWitnessLabel, h]

omit [Fintype σ] [DecidableEq σ] in
theorem stringVacTarget_realWitnessLabel (c : σ → Fin D) :
    stringVacTarget (realWitnessLabel c) = c := by
  funext i
  by_cases h : c i = 0
  · simp [stringVacTarget, realWitnessLabel, localVacTarget, h]
  · simp [stringVacTarget, realWitnessLabel, localVacTarget, h, Ne.symm h]

omit [DecidableEq σ] in
theorem stringVacCoeff_realWitnessLabel (c : σ → Fin D) :
    stringVacCoeff (realWitnessLabel c) = 1 := by
  rw [stringVacCoeff]
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases h : c i = 0
  · simp [realWitnessLabel, localVacCoeff, h]
  · simp [realWitnessLabel, localVacCoeff, h, Ne.symm h]

theorem quditStringSupport_imagWitnessLabel {c : σ → Fin D} {i₀ : σ} (h₀ : c i₀ ≠ 0) :
    quditStringSupport (imagWitnessLabel c i₀) = configSupport (0 : Fin D) c := by
  ext i
  rw [mem_quditStringSupport, mem_configSupport]
  by_cases hi : i = i₀
  · subst hi
    simp [imagWitnessLabel, h₀, Prod.ext_iff]
  · by_cases h : c i = 0 <;> simp [imagWitnessLabel, hi, h]

omit [Fintype σ] in
theorem stringVacTarget_imagWitnessLabel {c : σ → Fin D} {i₀ : σ} (h₀ : c i₀ ≠ 0) :
    stringVacTarget (imagWitnessLabel c i₀) = c := by
  funext i
  by_cases hi : i = i₀
  · subst hi
    simp [stringVacTarget, imagWitnessLabel, localVacTarget, h₀]
  · by_cases h : c i = 0
    · simp [stringVacTarget, imagWitnessLabel, localVacTarget, hi, h]
    · simp [stringVacTarget, imagWitnessLabel, localVacTarget, hi, h, Ne.symm h]

theorem stringVacCoeff_imagWitnessLabel {c : σ → Fin D} {i₀ : σ} (h₀ : c i₀ ≠ 0) :
    stringVacCoeff (imagWitnessLabel c i₀) = Complex.I := by
  rw [stringVacCoeff, Finset.prod_eq_single i₀]
  · simp [imagWitnessLabel, localVacCoeff, h₀]
  · intro b _ hb
    by_cases h : c b = 0
    · simp [imagWitnessLabel, localVacCoeff, hb, h]
    · simp [imagWitnessLabel, localVacCoeff, hb, h, Ne.symm h]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

end Witnesses


section VisibleRank

/-- Excitation configurations of weight between `1` and `q`. -/
abbrev ExcConfigLabel (σ : Type*) [Fintype σ] [DecidableEq σ] (D q : ℕ) [NeZero D] :=
  {c : σ → Fin D //
    0 < (configSupport (0 : Fin D) c).card ∧ (configSupport (0 : Fin D) c).card ≤ q}

/-- Real spanning family of the visible image: every excitation direction
together with its imaginary multiple. -/
noncomputable def excBasisFamily (q : ℕ) :
    (ExcConfigLabel σ D q ⊕ ExcConfigLabel σ D q) → ((σ → Fin D) → ℂ)
  | Sum.inl c => configBasis c.1
  | Sum.inr c => Complex.I • configBasis c.1

omit [DecidableEq σ] [NeZero D] in
theorem sum_smul_configBasis_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → (σ → Fin D)) (he : Function.Injective e) (g : ι → ℝ) (z : ℂ) (t : ι) :
    (∑ j : ι, g j • (z • configBasis (e j))) (e t) = (g t : ℂ) * z := by
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single t (fun b _ hb => by
    rw [Pi.smul_apply, Pi.smul_apply, configBasis_apply,
      if_neg (fun h => hb (he h.symm))]
    simp) (fun h => absurd (Finset.mem_univ t) h)]
  rw [Pi.smul_apply, Pi.smul_apply, configBasis_apply, if_pos rfl, smul_eq_mul,
    mul_one, Complex.real_smul]

/-- **The excitation directions are real-linearly independent.** -/
theorem linearIndependent_excBasisFamily (q : ℕ) :
    LinearIndependent ℝ (excBasisFamily (σ := σ) (D := D) q) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hval : ∀ t : ExcConfigLabel σ D q,
      ((g (Sum.inl t) : ℂ)) * 1 + (g (Sum.inr t) : ℂ) * Complex.I = 0 := by
    intro t
    have h := congrFun hg t.1
    rw [Fintype.sum_sum_type] at h
    have hinj : Function.Injective (fun c : ExcConfigLabel σ D q => c.1) :=
      fun x y hxy => Subtype.ext hxy
    have h1 : (∑ c : ExcConfigLabel σ D q, g (Sum.inl c) • excBasisFamily q (Sum.inl c)) t.1
        = (g (Sum.inl t) : ℂ) * 1 := by
      have := sum_smul_configBasis_apply (fun c : ExcConfigLabel σ D q => c.1) hinj
        (fun c => g (Sum.inl c)) 1 t
      simpa [excBasisFamily] using this
    have h2 : (∑ c : ExcConfigLabel σ D q, g (Sum.inr c) • excBasisFamily q (Sum.inr c)) t.1
        = (g (Sum.inr t) : ℂ) * Complex.I := by
      have := sum_smul_configBasis_apply (fun c : ExcConfigLabel σ D q => c.1) hinj
        (fun c => g (Sum.inr c)) Complex.I t
      simpa [excBasisFamily] using this
    rw [Pi.add_apply, h1, h2] at h
    exact h
  intro i
  cases i with
  | inl t =>
      have h := hval t
      have := congrArg Complex.re h
      simpa using this
  | inr t =>
      have h := hval t
      have := congrArg Complex.im h
      simpa using this

/-- The real span of the non-scalar Hermitian strings acting on at most `q`
sites. -/
noncomputable def qLocalDictionary (σ : Type*) [Fintype σ] [DecidableEq σ]
    (D q : ℕ) [NeZero D] : Submodule ℝ (Matrix (σ → Fin D) (σ → Fin D) ℂ) :=
  Submodule.span ℝ (Set.range (fun a : QLocalStringLabel σ D q => quditString a.1))

/-- The observer action of the product ground state, as a real-linear map. -/
noncomputable def vacuumObserverAction (σ : Type*) [Fintype σ] [DecidableEq σ]
    (D : ℕ) [NeZero D] :
    Matrix (σ → Fin D) (σ → Fin D) ℂ →ₗ[ℝ] ((σ → Fin D) → ℂ) :=
  (QuantumAlg.centeredLinear (quditVacuum : (σ → Fin D) → ℂ)).restrictScalars ℝ

theorem vacuumObserverAction_apply (A : Matrix (σ → Fin D) (σ → Fin D) ℂ) :
    vacuumObserverAction σ D A = QuantumAlg.centered (quditVacuum : (σ → Fin D) → ℂ) A :=
  rfl

omit [DecidableEq σ] in
/-- A configuration different from the ground configuration has nonempty
excitation support. -/
theorem card_configSupport_pos {c : σ → Fin D} (h : c ≠ fun _ => 0) :
    0 < (configSupport (0 : Fin D) c).card := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact Finset.card_pos.mpr ⟨i, mem_configSupport.mpr hi⟩

omit [DecidableEq σ] in
/-- A configuration with nonempty excitation support is not the ground
configuration. -/
theorem ne_ground_of_card_configSupport_pos {c : σ → Fin D}
    (h : 0 < (configSupport (0 : Fin D) c).card) : c ≠ fun _ => 0 := by
  intro hc
  obtain ⟨i, hi⟩ := Finset.card_pos.mp h
  exact (mem_configSupport.mp hi) (by rw [hc])

/-- **Visible image.**  The `q`-local dictionary acts on the product ground state
with image exactly the real span of the excitation directions of weight between
`1` and `q`. -/
theorem map_qLocalDictionary (q : ℕ) :
    (qLocalDictionary σ D q).map (vacuumObserverAction σ D)
      = Submodule.span ℝ (Set.range (excBasisFamily (σ := σ) (D := D) q)) := by
  classical
  rw [qLocalDictionary, Submodule.map_span]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, vacuumObserverAction_apply, centered_quditString_vacuum]
    by_cases h : stringVacTarget a.1 = fun _ : σ => 0
    · rw [if_pos h]
      exact Submodule.zero_mem _
    · rw [if_neg h]
      have hpos : 0 < (configSupport (0 : Fin D) (stringVacTarget a.1)).card :=
        card_configSupport_pos h
      have hle : (configSupport (0 : Fin D) (stringVacTarget a.1)).card ≤ q :=
        le_trans (Finset.card_le_card (configSupport_stringVacTarget_subset a.1)) a.2.2
      have hz : (stringVacCoeff a.1)
          = ((stringVacCoeff a.1).re : ℂ) + ((stringVacCoeff a.1).im : ℂ) * Complex.I :=
        (Complex.re_add_im _).symm
      have hsplit : stringVacCoeff a.1 • configBasis (stringVacTarget a.1)
          = (stringVacCoeff a.1).re • excBasisFamily q
              (Sum.inl (⟨stringVacTarget a.1, hpos, hle⟩ : ExcConfigLabel σ D q))
            + (stringVacCoeff a.1).im • excBasisFamily q
              (Sum.inr (⟨stringVacTarget a.1, hpos, hle⟩ : ExcConfigLabel σ D q)) := by
        funext x
        simp only [excBasisFamily, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Complex.real_smul]
        conv_lhs => rw [hz]
        ring
      rw [hsplit]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl _, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr _, rfl⟩))
  · rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe]
    refine Submodule.subset_span ?_
    cases x with
    | inl c =>
        have hsupp : quditStringSupport (realWitnessLabel c.1)
            = configSupport (0 : Fin D) c.1 := quditStringSupport_realWitnessLabel c.1
        refine ⟨quditString (realWitnessLabel c.1),
          ⟨⟨realWitnessLabel c.1, by rw [hsupp]; exact c.2.1, by rw [hsupp]; exact c.2.2⟩,
            rfl⟩, ?_⟩
        rw [vacuumObserverAction_apply, centered_quditString_vacuum,
          stringVacTarget_realWitnessLabel, stringVacCoeff_realWitnessLabel,
          if_neg (ne_ground_of_card_configSupport_pos c.2.1), one_smul]
        rfl
    | inr c =>
        obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp c.2.1
        have h₀ : c.1 i₀ ≠ 0 := mem_configSupport.mp hi₀
        have hsupp : quditStringSupport (imagWitnessLabel c.1 i₀)
            = configSupport (0 : Fin D) c.1 := quditStringSupport_imagWitnessLabel h₀
        refine ⟨quditString (imagWitnessLabel c.1 i₀),
          ⟨⟨imagWitnessLabel c.1 i₀, by rw [hsupp]; exact c.2.1,
            by rw [hsupp]; exact c.2.2⟩, rfl⟩, ?_⟩
        rw [vacuumObserverAction_apply, centered_quditString_vacuum,
          stringVacTarget_imagWitnessLabel h₀, stringVacCoeff_imagWitnessLabel h₀,
          if_neg (ne_ground_of_card_configSupport_pos c.2.1)]
        rfl

end VisibleRank


section RankLaws

/-- The number of excitation configurations of weight between `1` and `q`. -/
theorem card_ExcConfigLabel (q : ℕ) :
    Fintype.card (ExcConfigLabel σ D q)
      = ∑ k ∈ Finset.Icc 1 q, (Fintype.card σ).choose k * (D - 1) ^ k := by
  classical
  rw [Fintype.card_subtype]
  have h := card_configSupport_pos_le (σ := σ) (α := Fin D) (0 : Fin D) q
  rw [Fintype.card_fin] at h
  exact h

/-- **Observer-visible local-time dimension of a product state.**  The real rank
of the `q`-local dictionary action on the product ground state is twice the
number of excitation configurations of weight between `1` and `q`. -/
theorem finrank_map_qLocalDictionary (q : ℕ) :
    Module.finrank ℝ ↥((qLocalDictionary σ D q).map (vacuumObserverAction σ D))
      = 2 * ∑ k ∈ Finset.Icc 1 q, (Fintype.card σ).choose k * (D - 1) ^ k := by
  rw [map_qLocalDictionary, finrank_span_eq_card (linearIndependent_excBasisFamily q),
    Fintype.card_sum, card_ExcConfigLabel, two_mul]

/-- **Dictionary dimension.**  The non-scalar Hermitian strings acting on at most
`q` sites span a real space of the counted dimension. -/
theorem finrank_qLocalDictionary (q : ℕ) :
    Module.finrank ℝ ↥(qLocalDictionary σ D q)
      = ∑ k ∈ Finset.Icc 1 q, (Fintype.card σ).choose k * (D * D - 1) ^ k := by
  have hli : LinearIndependent ℝ (fun a : QLocalStringLabel σ D q => quditString a.1) :=
    linearIndependent_real_quditString.comp _ Subtype.val_injective
  rw [qLocalDictionary, finrank_span_eq_card hli, card_QLocalStringLabel]

instance : FiniteDimensional ℝ (Matrix (σ → Fin D) (σ → Fin D) ℂ) :=
  Module.Finite.trans (R := ℝ) ℂ (Matrix (σ → Fin D) (σ → Fin D) ℂ)

/-- **Invisible carrier dimension.**  The coefficient directions of the `q`-local
dictionary which the product ground state cannot see form a real space of
dimension the dictionary dimension minus the visible rank. -/
theorem finrank_ker_add_finrank_map_qLocalDictionary (q : ℕ) :
    Module.finrank ℝ
        ↥(LinearMap.ker ((vacuumObserverAction σ D).domRestrict (qLocalDictionary σ D q)))
      + 2 * ∑ k ∈ Finset.Icc 1 q, (Fintype.card σ).choose k * (D - 1) ^ k
      = ∑ k ∈ Finset.Icc 1 q, (Fintype.card σ).choose k * (D * D - 1) ^ k := by
  have hrn := LinearMap.finrank_range_add_finrank_ker
    ((vacuumObserverAction σ D).domRestrict (qLocalDictionary σ D q))
  rw [LinearMap.range_domRestrict] at hrn
  rw [finrank_map_qLocalDictionary] at hrn
  rw [← finrank_qLocalDictionary (σ := σ) (D := D) q, ← hrn]
  omega

/-- Qubit specialisation: the visible rank of a product state under the full
`q`-local Pauli dictionary. -/
theorem finrank_map_qLocalDictionary_qubit (q : ℕ) :
    Module.finrank ℝ ↥((qLocalDictionary σ 2 q).map (vacuumObserverAction σ 2))
      = 2 * ∑ k ∈ Finset.Icc 1 q, (Fintype.card σ).choose k := by
  rw [finrank_map_qLocalDictionary]
  simp

/-- Qubit specialisation: the dimension of the non-scalar `q`-local Pauli
dictionary. -/
theorem finrank_qLocalDictionary_qubit (q : ℕ) :
    Module.finrank ℝ ↥(qLocalDictionary σ 2 q)
      = ∑ k ∈ Finset.Icc 1 q, (Fintype.card σ).choose k * 3 ^ k := by
  rw [finrank_qLocalDictionary]

end RankLaws

end GaloisForLFunctions.HTGeometry
