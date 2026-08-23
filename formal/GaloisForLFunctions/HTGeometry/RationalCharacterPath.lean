import GaloisForLFunctions.HTGeometry.RationalCharacterApproximation
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.PathConnected

/-!
# Injective characters of a countable rational vector space are almost path-connected

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 9.4 (`t13`).

For a countable `ℚ`-vector space `V`, let `H = Hom (V, ℂˣ)` carry the topology of pointwise
convergence and let `H_inj` be the subspace of injective characters.  Any two characters of `V`
can be approximated by injective ones that are joined by a continuous path inside `H_inj`.

Both halves are proved here.  The approximation is the exponential construction of
`RationalCharacterApproximation`: a character is approximated by `exp ∘ ψ` for an injective
`ψ : V →ₗ[ℚ] ℂ` whose image meets `ℚ · 2πi` only in `0`.  For the path, the affine segment
`ψ_z = (1 - z) ψ₀ + z ψ₁` fails to avoid the periods only for `z` in a countable set — for each
nonzero `v` and each integer `k` the equation `ψ_z (v) = 2πik` has at most one solution, and none
at all when `ψ₀ (v) = ψ₁ (v)` — and the complement of a countable subset of `ℂ` is path connected.
-/

namespace HTGeometry

open Filter Topology Set

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The character `exp ∘ ψ` attached to a `ℚ`-linear map `V → ℂ`. -/
noncomputable def deningerExpChar (ψ : V →ₗ[ℚ] ℂ) : V → ℂˣ :=
  fun v => Units.mk0 (Complex.exp (ψ v)) (Complex.exp_ne_zero _)

@[simp] theorem deningerExpChar_val (ψ : V →ₗ[ℚ] ℂ) (v : V) :
    (deningerExpChar ψ v : ℂ) = Complex.exp (ψ v) := rfl

theorem deningerExpChar_mul (ψ : V →ₗ[ℚ] ℂ) (a b : V) :
    deningerExpChar ψ (a + b) = deningerExpChar ψ a * deningerExpChar ψ b := by
  apply Units.ext
  simp [Complex.exp_add]

/-- The period line `ℚ · 2πi` in `ℂ`. -/
noncomputable def deningerPeriodLine : Submodule ℚ ℂ :=
  Submodule.span ℚ ({2 * (Real.pi : ℂ) * Complex.I} : Set ℂ)

theorem deningerPeriodLine_generator_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- A linear map `V → ℂ` *avoids the periods* when no nonzero vector is sent to an integer
multiple of `2πi`. -/
def DeningerAvoidsPeriods (ψ : V →ₗ[ℚ] ℂ) : Prop :=
  ∀ v : V, (∃ k : ℤ, ψ v = (k : ℤ) • (2 * (Real.pi : ℂ) * Complex.I)) → v = 0

theorem deningerAvoidsPeriods_of_periodLine {ψ : V →ₗ[ℚ] ℂ}
    (h : ∀ v : V, ψ v ∈ deningerPeriodLine → v = 0) : DeningerAvoidsPeriods ψ := by
  rintro v ⟨k, hk⟩
  refine h v ?_
  rw [hk, deningerPeriodLine]
  exact zsmul_mem (Submodule.mem_span_singleton_self _) k

theorem deningerExpChar_injective (ψ : V →ₗ[ℚ] ℂ) (h : DeningerAvoidsPeriods ψ) :
    Function.Injective (deningerExpChar ψ) := by
  intro a b hab
  have h1 : Complex.exp (ψ a) = Complex.exp (ψ b) := congrArg Units.val hab
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h1
  have h2 : ψ (a - b) = (k : ℤ) • (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [map_sub, hk, zsmul_eq_mul]; ring
  exact sub_eq_zero.1 (h (a - b) ⟨k, h2⟩)

/-- **Deninger, Lemma 9.4, approximation step.**  Every character of a countable `ℚ`-vector space
is approximated, in the topology of pointwise convergence, by a character of the form `exp ∘ ψ`
with `ψ` linear and avoiding the period line — in particular by an injective character. -/
theorem exists_expChar_mem_nhds [Countable V] (φ : V → ℂˣ)
    (hφ : ∀ a b, φ (a + b) = φ a * φ b) {U : Set (V → ℂˣ)} (hU : U ∈ 𝓝 φ) :
    ∃ ψ : V →ₗ[ℚ] ℂ, (∀ v : V, ψ v ∈ deningerPeriodLine → v = 0) ∧ deningerExpChar ψ ∈ U := by
  classical
  obtain ⟨S, ε, hε, hSU⟩ := deningerChar_exists_basic_nhds φ hU
  obtain ⟨n, e, he, hrep⟩ := exists_integral_basis_of_finset S
  -- powers of a character
  have hφ0 : φ 0 = 1 := by
    have h := hφ 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := φ 0) (by rw [mul_one]; exact h.symm)
  have hφneg : ∀ v : V, φ (-v) = (φ v)⁻¹ := by
    intro v
    have h := hφ v (-v)
    rw [add_neg_cancel, hφ0] at h
    exact (eq_inv_of_mul_eq_one_right h.symm)
  have hφz : ∀ (k : ℤ) (v : V), φ (k • v) = (φ v) ^ k := by
    intro k v
    induction k using Int.induction_on with
    | zero => simpa using hφ0
    | succ m ih =>
      rw [add_smul, one_smul, hφ, ih, zpow_add_one]
    | pred m ih =>
      rw [sub_smul, one_smul, sub_eq_add_neg, hφ, hφneg, ih, zpow_sub_one]
  have hφsum : ∀ (t : Finset (Fin n)) (c : Fin n → ℤ),
      φ (∑ i ∈ t, c i • e i) = ∏ i ∈ t, (φ (e i)) ^ (c i) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro c; simpa using hφ0
    | insert a t ha ih =>
      intro c
      rw [Finset.sum_insert ha, hφ, hφz, ih, Finset.prod_insert ha]
  -- logarithms of the values on the basis
  have hulog : ∀ i : Fin n, ∃ z : ℂ, Complex.exp z = (φ (e i) : ℂ) := by
    intro i
    have hmem : ((φ (e i) : ℂ)) ∈ Set.range Complex.exp := by
      rw [Complex.range_exp]
      simp [Units.ne_zero]
    exact hmem
  choose u hu using hulog
  -- the finitely many integral coordinate vectors
  have hrep' : ∀ s : (S : Finset V), ∃ c : Fin n → ℤ, (s : V) = ∑ i, c i • e i :=
    fun s => hrep s.1 s.2
  choose cc hcc using hrep'
  -- the evaluation maps and the modulus of continuity
  set F : (Fin n → ℤ) → (Fin n → ℂ) → ℂ :=
    fun c v => Complex.exp (∑ i, (c i : ℂ) * v i) with hF
  have hFcont : ∀ c : Fin n → ℤ, Continuous (F c) := by
    intro c
    exact Complex.continuous_exp.comp
      (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))
  set T : Set (Fin n → ℂ) :=
    ⋂ s : (S : Finset V), {v | dist (F (cc s) v) (F (cc s) u) < ε} with hT
  have hTopen : IsOpen T := by
    refine isOpen_iInter_of_finite fun s => ?_
    exact isOpen_lt (((hFcont (cc s)).dist continuous_const)) continuous_const
  have hTu : u ∈ T := by
    simp only [hT, Set.mem_iInter, Set.mem_setOf_eq, dist_self]
    exact fun s => hε
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hTopen u hTu
  -- perturb into an independent family
  obtain ⟨w, hwd, hwi⟩ :=
    exists_linearIndependent_near (2 * (Real.pi : ℂ) * Complex.I)
      deningerPeriodLine_generator_ne_zero n u δ hδ
  have hwT : w ∈ T := by
    refine hball ?_
    rw [Metric.mem_ball, dist_pi_lt_iff hδ]
    exact hwd
  obtain ⟨ψ, hψe, -, hψavoid⟩ :=
    exists_linear_extension_avoiding (2 * (Real.pi : ℂ) * Complex.I) e he w
      (linearIndependent_finCons.2 hwi)
  refine ⟨ψ, hψavoid, ?_⟩
  refine hSU _ ?_
  intro s hs
  obtain ⟨c, hc, hmemT⟩ : ∃ c : Fin n → ℤ, s = ∑ i, c i • e i ∧ dist (F c w) (F c u) < ε :=
    ⟨cc ⟨s, hs⟩, hcc ⟨s, hs⟩, Set.mem_iInter.1 hwT ⟨s, hs⟩⟩
  have h1 : ((deningerExpChar ψ) s : ℂ) = F c w := by
    rw [deningerExpChar_val, hF]
    simp only
    rw [hc]
    congr 1
    rw [map_sum ψ (fun i => c i • e i) Finset.univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hψe i, zsmul_eq_mul]
  have h3 : ((φ s : ℂ)) = F c u := by
    rw [hc, hφsum Finset.univ, hF]
    simp only
    rw [Complex.exp_sum]
    have hprod : ((∏ i, (φ (e i)) ^ (c i) : ℂˣ) : ℂ)
        = ∏ i, (((φ (e i)) ^ (c i) : ℂˣ) : ℂ) := by
      simp
    rw [hprod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, ← hu i, ← Complex.exp_int_mul]
  rw [h1, h3]
  exact hmemT

/-! ### Lemma 9.4 -/

/-- The characters `V → ℂˣ`, as a subspace of the space of all maps with the topology of
pointwise convergence. -/
def deningerCharSet (V : Type*) [AddCommGroup V] : Set (V → ℂˣ) :=
  {φ | ∀ a b, φ (a + b) = φ a * φ b}

/-- The injective characters. -/
def deningerCharInjSet (V : Type*) [AddCommGroup V] : Set (V → ℂˣ) :=
  {φ | (∀ a b, φ (a + b) = φ a * φ b) ∧ Function.Injective φ}

theorem deningerExpChar_mem_charInjSet {ψ : V →ₗ[ℚ] ℂ} (h : DeningerAvoidsPeriods ψ) :
    deningerExpChar ψ ∈ deningerCharInjSet V :=
  ⟨deningerExpChar_mul ψ, deningerExpChar_injective ψ h⟩

/-- The affine segment of linear maps between two linear maps, evaluated at a complex parameter. -/
noncomputable def deningerSegment (ψ₀ ψ₁ : V →ₗ[ℚ] ℂ) (z : ℂ) : V →ₗ[ℚ] ℂ :=
  (1 - z) • ψ₀ + z • ψ₁

@[simp] theorem deningerSegment_apply (ψ₀ ψ₁ : V →ₗ[ℚ] ℂ) (z : ℂ) (v : V) :
    deningerSegment ψ₀ ψ₁ z v = (1 - z) * ψ₀ v + z * ψ₁ v := rfl

theorem deningerSegment_zero (ψ₀ ψ₁ : V →ₗ[ℚ] ℂ) : deningerSegment ψ₀ ψ₁ 0 = ψ₀ := by
  ext v; simp

theorem deningerSegment_one (ψ₀ ψ₁ : V →ₗ[ℚ] ℂ) : deningerSegment ψ₀ ψ₁ 1 = ψ₁ := by
  ext v; simp

/-- The exceptional set of parameters at which the segment fails to avoid the periods. -/
def deningerBadSet (ψ₀ ψ₁ : V →ₗ[ℚ] ℂ) : Set ℂ :=
  {z | ∃ v : V, v ≠ 0 ∧ ∃ k : ℤ,
    deningerSegment ψ₀ ψ₁ z v = (k : ℤ) • (2 * (Real.pi : ℂ) * Complex.I)}

theorem deningerBadSet_countable [Countable V] {ψ₀ ψ₁ : V →ₗ[ℚ] ℂ}
    (h₀ : DeningerAvoidsPeriods ψ₀) : (deningerBadSet ψ₀ ψ₁).Countable := by
  refine Set.Countable.mono ?_
    (Set.countable_range (fun p : V × ℤ =>
      (((p.2 : ℤ) • (2 * (Real.pi : ℂ) * Complex.I) - ψ₀ p.1) / (ψ₁ p.1 - ψ₀ p.1))))
  rintro z ⟨v, hv, k, hk⟩
  rw [deningerSegment_apply] at hk
  have hne : ψ₁ v - ψ₀ v ≠ 0 := by
    intro hzero
    have hsub : ψ₁ v = ψ₀ v := sub_eq_zero.1 hzero
    refine hv (h₀ v ⟨k, ?_⟩)
    rw [← hk, hsub]
    ring
  refine ⟨(v, k), ?_⟩
  field_simp
  rw [← hk]
  ring

theorem deningerBadSet_zero_notMem {ψ₀ ψ₁ : V →ₗ[ℚ] ℂ} (h₀ : DeningerAvoidsPeriods ψ₀) :
    (0 : ℂ) ∉ deningerBadSet ψ₀ ψ₁ := by
  rintro ⟨v, hv, k, hk⟩
  rw [deningerSegment_zero] at hk
  exact hv (h₀ v ⟨k, hk⟩)

theorem deningerBadSet_one_notMem {ψ₀ ψ₁ : V →ₗ[ℚ] ℂ} (h₁ : DeningerAvoidsPeriods ψ₁) :
    (1 : ℂ) ∉ deningerBadSet ψ₀ ψ₁ := by
  rintro ⟨v, hv, k, hk⟩
  rw [deningerSegment_one] at hk
  exact hv (h₁ v ⟨k, hk⟩)

/-- **Deninger, Lemma 9.4 (`t13`).**  For any two characters of a countable `ℚ`-vector space and
any neighbourhoods of them in the topology of pointwise convergence there are injective characters
in those neighbourhoods that are joined by a continuous path of injective characters. -/
theorem deningerChar_lemma94 [Countable V] {φ₀ φ₁ : V → ℂˣ}
    (h₀ : φ₀ ∈ deningerCharSet V) (h₁ : φ₁ ∈ deningerCharSet V)
    {U₀ U₁ : Set (V → ℂˣ)} (hU₀ : U₀ ∈ 𝓝 φ₀) (hU₁ : U₁ ∈ 𝓝 φ₁) :
    ∃ χ₀ ∈ U₀ ∩ deningerCharInjSet V, ∃ χ₁ ∈ U₁ ∩ deningerCharInjSet V,
      ∃ γ : unitInterval → (V → ℂˣ), Continuous γ ∧ γ 0 = χ₀ ∧ γ 1 = χ₁ ∧
        ∀ t, γ t ∈ deningerCharInjSet V := by
  obtain ⟨ψ₀, hψ₀, hmem₀⟩ := exists_expChar_mem_nhds φ₀ h₀ hU₀
  obtain ⟨ψ₁, hψ₁, hmem₁⟩ := exists_expChar_mem_nhds φ₁ h₁ hU₁
  have ha₀ : DeningerAvoidsPeriods ψ₀ := deningerAvoidsPeriods_of_periodLine hψ₀
  have ha₁ : DeningerAvoidsPeriods ψ₁ := deningerAvoidsPeriods_of_periodLine hψ₁
  -- a path in the complement of the exceptional set
  have hcount : (deningerBadSet ψ₀ ψ₁).Countable := deningerBadSet_countable ha₀
  have hrank : 1 < Module.rank ℝ ℂ := Complex.rank_real_complex ▸ Nat.one_lt_ofNat
  have hpc : IsPathConnected (deningerBadSet ψ₀ ψ₁)ᶜ :=
    Set.Countable.isPathConnected_compl_of_one_lt_rank hrank hcount
  obtain ⟨α, hα⟩ : JoinedIn (deningerBadSet ψ₀ ψ₁)ᶜ 0 1 :=
    hpc.joinedIn 0 (deningerBadSet_zero_notMem ha₀) 1 (deningerBadSet_one_notMem ha₁)
  -- the path of characters
  have hseg : ∀ t : unitInterval, DeningerAvoidsPeriods (deningerSegment ψ₀ ψ₁ (α t)) := by
    intro t v hv
    by_contra hvne
    exact hα t ⟨v, hvne, hv⟩
  refine ⟨deningerExpChar ψ₀, ⟨hmem₀, deningerExpChar_mem_charInjSet ha₀⟩,
    deningerExpChar ψ₁, ⟨hmem₁, deningerExpChar_mem_charInjSet ha₁⟩,
    fun t => deningerExpChar (deningerSegment ψ₀ ψ₁ (α t)), ?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun v => ?_
    rw [Units.isEmbedding_val₀.toIsInducing.continuous_iff]
    exact Complex.continuous_exp.comp
      (((continuous_const.sub (α.continuous)).mul continuous_const).add
        (α.continuous.mul continuous_const))
  · show deningerExpChar (deningerSegment ψ₀ ψ₁ (α 0)) = deningerExpChar ψ₀
    rw [α.source, deningerSegment_zero]
  · show deningerExpChar (deningerSegment ψ₀ ψ₁ (α 1)) = deningerExpChar ψ₁
    rw [α.target, deningerSegment_one]
  · exact fun t => deningerExpChar_mem_charInjSet (hseg t)

end HTGeometry
